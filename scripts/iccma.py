#!/usr/bin/env python3
"""Run ananas on ICCMA'25 instances and compare with the competition results.

    scripts/iccma.py select TASK [--per-family N] [--hard] [--all]
    scripts/iccma.py run TASK [instances...] [--all] [--timeout S] [--jobs J]
                         [--solver NAME=COMMAND ...]

`select` prints instance names, one per line, chosen from the results
file: per family, the easiest, a middle and the hardest instance by
fudge's time (--per-family), plus every instance affca timed out on
(--hard), or every instance of the task (--all). `run` solves the given instances (or those from `select` with
default settings when none are given) with ananas and prints, per
instance, ananas's answer and time next to the reference answer -- the
one fudge and mutoksia agree on -- and their times. Answers are verified
with VE-CO/VE-ST where ananas says YES, and compared with the reference
otherwise. With --solver, other solvers run on the same instances and
under the same time limit, one after the other within each job, called
with the ICCMA interface (COMMAND -p TASK -f FILE [-a ARG]); a solver
named fudge or mutoksia then replaces its times from the results file.
Their YES answers are verified with ananas, their NO answers compared
with the reference. It ends with a summary over the instances run: per solver the
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
import shlex
import signal
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


def timed(command, timeout):
    """Run `command`; returns (stdout, seconds), or (None, timeout) if it
    timed out, in which case it is killed with everything it started"""
    started = time.time()
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                               text=True, start_new_session=True)
    try:
        stdout, _ = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.communicate()
        return None, timeout
    return stdout, time.time() - started


def verify(task, path, stdout):
    """Whether the witness in a YES answer's output is an extension of the
    task's semantics containing the query, checked by ananas. Returns None
    for DC answers without a witness, which cannot be checked."""
    witness = [line for line in stdout.splitlines() if line.startswith('w')]
    if not witness:
        return None
    with tempfile.NamedTemporaryFile('w', suffix='.out', delete=False) as f:
        f.write('YES\n' + witness[0] + '\n')
        name = f.name
    check = subprocess.run([ANANAS, '-p', 'VE-' + task.split('-')[1], '-i', path, '-e', name],
                           capture_output=True, text=True)
    os.unlink(name)
    return check.stdout.strip() == 'YES'


def answer_of(stdout):
    """The answer in a solver's output: YES or NO, a witness line meaning
    YES, or ERROR"""
    for line in stdout.splitlines():
        line = line.strip()
        if line in ('YES', 'NO'):
            return line
        if line.startswith('w'):
            return 'YES'
        if line:
            return 'ERROR'
    return 'ERROR'


def run_one(task, instance, timeout, solver=None):
    """Solve one instance with ananas, or with the ICCMA-interface command
    `solver`; returns (answer, seconds, verified)"""
    path = os.path.join(AFS, instance)
    if solver is None:
        command = [ANANAS, '-p', task, '-i', path]
    else:
        command = shlex.split(solver) + ['-p', task, '-f', path]
    if task.startswith('DC-'):
        command += ['-a', query_of(instance)]
    stdout, seconds = timed(command, timeout)
    if stdout is None:
        return 'TIMEOUT', seconds, None
    answer = answer_of(stdout)
    if answer == 'ERROR':
        print(f"[{solver or 'ananas'} on {instance}] {stdout.strip()[:200]!r}", file=sys.stderr, flush=True)
    return answer, seconds, verify(task, path, stdout) if answer == 'YES' else None


def judge(answer, verified, ref):
    """What is wrong with an answer, or what is notable about it: a note
    for the output, and whether the answer counts as solved"""
    if answer == 'YES' and verified is False:
        return 'INVALID WITNESS', False
    if answer in ('YES', 'NO') and ref in ('YES', 'NO') and answer != ref:
        return 'WRONG', False
    if answer not in ('YES', 'NO'):
        return '', False
    if answer == 'YES' and verified:
        return 'verified', True
    if ref == '?':
        return 'unconfirmed', True
    return '', True


def run(task, instances, timeout, jobs, others=None):
    """Solve `instances` with ananas, and with the solvers in `others`
    (name -> ICCMA-interface command), comparing with the results file
    for the competition solvers not run"""
    others = others or {}
    by = load_results(task)
    columns = list(REFERENCE_SOLVERS) + [s for s in others if s not in REFERENCE_SOLVERS]
    header = ''.join(f" {s + ('*' if s in others else ''):>9s}" for s in columns)
    print(f"{'instance':44s} {'ref':4s} {'ananas':8s} {'time':>8s}{header}  note", flush=True)
    if others:
        print(f"(* run here under the same limit: {', '.join(others)})", flush=True)
    wrong = collections.Counter()
    # Per solver and instance: the time if solved within the limit, else None
    solved = {s: {} for s in ['ananas'] + columns}

    def solve(instance):
        mine = run_one(task, instance, timeout)
        theirs = {s: run_one(task, instance, timeout, command) for s, command in others.items()}
        return instance, mine, theirs

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for instance, (answer, seconds, verified), theirs in pool.map(solve, instances):
            results = by.get(instance, {})
            ref = reference(results) or '?'
            note, ok = judge(answer, verified, ref)
            if note in ('INVALID WITNESS', 'WRONG'):
                wrong['ananas'] += 1
            solved['ananas'][instance] = seconds if ok else None
            cells = []
            for s in columns:
                if s in theirs:
                    their_answer, t, their_verified = theirs[s]
                    their_note, their_ok = judge(their_answer, their_verified, ref)
                    if their_note in ('INVALID WITNESS', 'WRONG'):
                        wrong[s] += 1
                        note += f" {s}:{their_note}"
                    elif their_answer not in ('YES', 'NO', 'TIMEOUT'):
                        note += f" {s}:{their_answer}"
                    elif their_ok and answer in ('YES', 'NO') and their_answer != answer:
                        note += f" {s}:DISAGREES"
                    solved[s][instance] = t if their_ok else None
                    cells.append(t if their_answer != 'TIMEOUT' else None)
                else:
                    t = solver_time(results, s)
                    solved[s][instance] = t if t is not None and t <= timeout else None
                    cells.append(t)
            fmt = lambda t: f" {t:9.2f}" if t is not None else f" {'timeout':>9s}"
            print(f"{instance:44s} {ref:4s} {answer:8s} {seconds:8.2f}{''.join(fmt(t) for t in cells)}  {note.strip()}",
                  flush=True)
    print(f"\n{len(instances)} instances, {wrong['ananas']} wrong")
    summarize(task, instances, solved, timeout, wrong, others)
    return wrong['ananas'] == 0


def summarize(task, instances, solved, timeout, wrong, others):
    """Solved counts and PAR2 per solver, overall and per family"""
    print(f"\n{task}, {len(instances)} instances, time limit {timeout:g}s")
    for s in solved:
        if s != 'ananas':
            where = 'run here' if s in others else 'from the results file, capped at the same limit'
            print(f"  {s}: {where}")
    print(f"{'solver':10s} {'solved':>6s} {'unsolved':>8s} {'wrong':>5s} {'PAR2':>10s} {'fastest':>7s}")
    fastest = collections.Counter()
    for i in instances:
        times = {s: solved[s][i] for s in solved if solved[s][i] is not None}
        if times:
            fastest[min(times, key=times.get)] += 1
    for s in solved:
        ts = [solved[s][i] for i in instances]
        done = [t for t in ts if t is not None]
        par2 = sum(done) + 2 * timeout * (len(ts) - len(done))
        print(f"{s:10s} {len(done):6d} {len(ts) - len(done):8d} {wrong[s]:5d} {par2:10.0f} {fastest[s]:7d}")
    only = lambda a, b: sum(1 for i in instances if solved[a][i] is not None and solved[b][i] is None)
    for other in (s for s in solved if s != 'ananas'):
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
    r.add_argument('--solver', action='append', default=[], metavar='NAME=COMMAND',
                   help='also run this ICCMA-interface solver; repeatable')
    args = parser.parse_args()
    if args.command == 'select':
        print('\n'.join(select(args.task, args.per_family, args.hard, args.all)))
    else:
        instances = args.instances or select(args.task, 3, True, args.all)
        others = dict(spec.split('=', 1) for spec in args.solver)
        sys.exit(0 if run(args.task, instances, args.timeout, args.jobs, others) else 1)


if __name__ == '__main__':
    main()
