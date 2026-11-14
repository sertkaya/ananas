#!/usr/bin/env python3
"""Run ananas on ICCMA'25 instances and compare with the competition results.

    scripts/iccma.py select TASK [--per-family N] [--hard]   list instances
    scripts/iccma.py run TASK [instances...] [--timeout S] [--jobs J]

`select` prints instance names, one per line, chosen from the results
file: per family, the easiest, a middle and the hardest instance by
fudge's time (--per-family), plus every instance affca timed out on
(--hard). `run` solves the given instances (or those from `select` with
default settings when none are given) with ananas and prints, per
instance, ananas's answer and time next to the reference answer -- the
one fudge and mutoksia agree on -- and their times. Answers are verified
with VE-CO/VE-ST where ananas says YES, and compared with the reference
otherwise. Exit status is 1 if any answer is wrong.

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


def select(task, per_family, hard):
    """Instances spanning the families and difficulties of `task`"""
    by = load_results(task)
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
    print(f"{'instance':44s} {'ref':4s} {'ananas':8s} {'time':>8s} {'fudge':>8s} {'mutoksia':>8s}  note")
    wrong = 0
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
            fmt = lambda t: f"{t:8.2f}" if t is not None else f"{'timeout':>8s}"
            print(f"{instance:44s} {ref:4s} {answer:8s} {seconds:8.2f} {fmt(times[0])} {fmt(times[1])}  {note}")
    print(f"\n{len(instances)} instances, {wrong} wrong")
    return wrong == 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    s = sub.add_parser('select')
    s.add_argument('task')
    s.add_argument('--per-family', type=int, default=3)
    s.add_argument('--hard', action='store_true')
    r = sub.add_parser('run')
    r.add_argument('task')
    r.add_argument('instances', nargs='*')
    r.add_argument('--timeout', type=float, default=60)
    r.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    if args.command == 'select':
        print('\n'.join(select(args.task, args.per_family, args.hard)))
    else:
        instances = args.instances or select(args.task, 3, True)
        sys.exit(0 if run(args.task, instances, args.timeout, args.jobs) else 1)


if __name__ == '__main__':
    main()
