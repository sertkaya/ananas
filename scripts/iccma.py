#!/usr/bin/env python3
"""Run ananas on ICCMA'25 instances and compare with the competition results.

    scripts/iccma.py select TASK [--per-family N] [--hard] [--all]
    scripts/iccma.py run TASK [instances...] [--all] [--timeout S] [--jobs J]

`select` prints instance names, one per line, chosen from the results
file: per family, the easiest, a middle and the hardest instance by
fudge's time (--per-family), plus every instance affca timed out on
(--hard), or every instance of the task (--all). `run` solves the given instances (or those from `select` with
default settings when none are given) with ananas and prints, per
instance, ananas's answer and time next to the reference answer -- the
one fudge and mutoksia agree on -- and their times. Answers are verified
with VE-CO/VE-ST where ananas says YES, and compared with the reference
otherwise. It ends with a summary over the instances run: per solver the
number solved within the time limit -- the competition solvers' times
from the results file, capped at the same limit -- the timeouts, wrong
answers and PAR2 score, and the instances solved per family. Exit status
is 1 if any answer is wrong.

The benchmark directory is iccma2025-benchmarks/ next to this repository's
root, with AFs/ holding the .af and .arg files and the results CSV.
"""

import argparse
import collections
import csv
import os
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, 'iccma2025-benchmarks')
AFS = os.path.join(BENCH, 'AFs')
RESULTS = os.path.join(BENCH, 'iccma25_main_results.csv')
ANANAS = os.path.join(ROOT, 'target', 'release', 'ananas')
REFERENCE_SOLVERS = ('fudge', 'mutoksia')


def family(instance):
    """The generator family an instance name belongs to"""
    stem = re.sub(r'\.af$', '', instance)
    return re.sub(r'[_-]?[0-9].*$', '', stem) or stem


def load_results(task):
    """Per instance, the results of every solver on `task`"""
    by = collections.defaultdict(dict)
    with open(RESULTS) as f:
        for row in csv.DictReader(f, delimiter=';'):
            if row['TASK'] == task:
                by[row['INSTANCE']][row['SOLVER']] = row
    return by


def reference(results):
    """The answer fudge and mutoksia agree on, or None. For SE tasks the
    results file records a found extension as NA without a timeout, which
    counts as YES."""
    answers = set()
    for solver in REFERENCE_SOLVERS:
        row = results.get(solver)
        if row is None or row['TIMEOUT'] == 'true':
            return None
        answer = row['ANSWER']
        if answer == 'NA' and row['TASK'].startswith('SE-'):
            answer = 'YES'
        answers.add(answer)
    if len(answers) == 1 and (answer := answers.pop()) in ('YES', 'NO'):
        return answer
    return None


def solver_time(results, solver):
    """A solver's wall time, or None if it timed out"""
    row = results.get(solver)
    if row is None or row['TIMEOUT'] == 'true':
        return None
    return float(row['WCTIME'])


def select(task, per_family, hard, every=False):
    """Instances spanning the families and difficulties of `task`, or all
    of them if `every`"""
    by = load_results(task)
    if every:
        return sorted(by)
    chosen = []
    families = collections.defaultdict(list)
    for instance, results in by.items():
        if reference(results) is None:
            continue
        families[family(instance)].append(instance)
    for members in families.values():
        members.sort(key=lambda i: solver_time(by[i], 'fudge') or float('inf'))
        if per_family >= len(members):
            picks = members
        else:
            picks = [members[round(k * (len(members) - 1) / max(per_family - 1, 1))] for k in range(per_family)]
        chosen.extend(picks)
    if hard:
        chosen.extend(i for i, r in by.items() if r.get('affca', {}).get('TIMEOUT') == 'true' and reference(r))
    return sorted(set(chosen))


def query_of(instance):
    """The argument the instance's .arg file names"""
    with open(os.path.join(AFS, instance + '.arg')) as f:
        return f.read().strip()


def run_one(task, instance, timeout):
    """Solve one instance with ananas; returns (answer, seconds, verified)"""
    path = os.path.join(AFS, instance)
    command = [ANANAS, '-p', task, '-i', path]
    if task.startswith('DC-'):
        command += ['-a', query_of(instance)]
    started = time.time()
    try:
        completed = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', timeout, None
    seconds = time.time() - started
    lines = completed.stdout.splitlines()
    answer = lines[0] if lines else 'ERROR'
    verified = None
    if answer == 'YES':
        verify = {'DC-CO': 'VE-CO', 'DC-ST': 'VE-ST', 'SE-ST': 'VE-ST'}[task]
        with tempfile.NamedTemporaryFile('w', suffix='.out', delete=False) as f:
            f.write(completed.stdout)
            witness = f.name
        check = subprocess.run([ANANAS, '-p', verify, '-i', path, '-e', witness], capture_output=True, text=True)
        os.unlink(witness)
        verified = check.stdout.strip() == 'YES'
    return answer, seconds, verified


def run(task, instances, timeout, jobs):
    by = load_results(task)
    print(f"{'instance':44s} {'ref':4s} {'ananas':8s} {'time':>8s} {'fudge':>8s} {'mutoksia':>8s}  note", flush=True)
    wrong = 0
    # Per solver and instance: the time if solved within the limit, else None
    solved = {s: {} for s in ('ananas',) + REFERENCE_SOLVERS}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        outcomes = pool.map(lambda i: (i, run_one(task, i, timeout)), instances)
        for instance, (answer, seconds, verified) in outcomes:
            results = by.get(instance, {})
            ref = reference(results) or '?'
            times = [solver_time(results, s) for s in REFERENCE_SOLVERS]
            note = ''
            if answer == 'YES' and verified is False:
                note, wrong = 'INVALID WITNESS', wrong + 1
            elif answer in ('YES', 'NO') and ref in ('YES', 'NO') and answer != ref:
                note, wrong = 'WRONG', wrong + 1
            elif answer == 'YES':
                note = 'verified'
            elif answer == 'NO' and ref == '?':
                note = 'unconfirmed'
            ok = answer in ('YES', 'NO') and note not in ('INVALID WITNESS', 'WRONG')
            solved['ananas'][instance] = seconds if ok else None
            for s, t in zip(REFERENCE_SOLVERS, times):
                solved[s][instance] = t if t is not None and t <= timeout else None
            fmt = lambda t: f"{t:8.2f}" if t is not None else f"{'timeout':>8s}"
            print(f"{instance:44s} {ref:4s} {answer:8s} {seconds:8.2f} {fmt(times[0])} {fmt(times[1])}  {note}", flush=True)
    print(f"\n{len(instances)} instances, {wrong} wrong")
    summarize(task, instances, solved, timeout, wrong)
    return wrong == 0


def summarize(task, instances, solved, timeout, wrong):
    """Solved counts and PAR2 per solver, overall and per family"""
    print(f"\n{task}, {len(instances)} instances, time limit {timeout:g}s "
          f"(competition times capped at the same limit)")
    print(f"{'solver':10s} {'solved':>6s} {'unsolved':>8s} {'PAR2':>10s} {'fastest':>7s}")
    fastest = collections.Counter()
    for i in instances:
        times = {s: solved[s][i] for s in solved if solved[s][i] is not None}
        if times:
            fastest[min(times, key=times.get)] += 1
    for s in solved:
        ts = [solved[s][i] for i in instances]
        done = [t for t in ts if t is not None]
        par2 = sum(done) + 2 * timeout * (len(ts) - len(done))
        print(f"{s:10s} {len(done):6d} {len(ts) - len(done):8d} {par2:10.0f} {fastest[s]:7d}")
    print(f"ananas wrong answers: {wrong}")
    only = lambda a, b: sum(1 for i in instances if solved[a][i] is not None and solved[b][i] is None)
    for other in REFERENCE_SOLVERS:
        print(f"solved by ananas but not {other}: {only('ananas', other)}, by {other} but not ananas: {only(other, 'ananas')}")
    families = collections.defaultdict(list)
    for i in instances:
        families[family(i)].append(i)
    print(f"\n{'family':24s} {'n':>4s}" + ''.join(f" {s:>8s}" for s in solved))
    for f in sorted(families):
        members = families[f]
        counts = ''.join(f" {sum(1 for i in members if solved[s][i] is not None):8d}" for s in solved)
        print(f"{f[:24]:24s} {len(members):4d}{counts}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    s = sub.add_parser('select')
    s.add_argument('task')
    s.add_argument('--per-family', type=int, default=3)
    s.add_argument('--hard', action='store_true')
    s.add_argument('--all', action='store_true')
    r = sub.add_parser('run')
    r.add_argument('task')
    r.add_argument('instances', nargs='*')
    r.add_argument('--all', action='store_true')
    r.add_argument('--timeout', type=float, default=60)
    r.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    if args.command == 'select':
        print('\n'.join(select(args.task, args.per_family, args.hard, args.all)))
    else:
        instances = args.instances or select(args.task, 3, True, args.all)
        sys.exit(0 if run(args.task, instances, args.timeout, args.jobs) else 1)


if __name__ == '__main__':
    main()
