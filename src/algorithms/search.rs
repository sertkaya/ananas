//! The search every problem shares: conflict-driven clause learning on top
//! of the closure's propagation.
//!
//! A `Solver` looks for an extension, under its semantics, that contains a
//! given set of assumed arguments. It decides one argument at a time, lets
//! the closure propagate, and on a conflict learns a clause, jumps back to
//! the level where that clause becomes unit, and asserts it. The learned
//! clauses hold for every extension containing the assumptions, so a solver
//! can be asked again with a larger set of assumptions and keep them.

use std::collections::HashSet;
use std::time::Instant;
use crate::af::AF;
use crate::algorithms::activity::Activity;
use crate::algorithms::clauses::ClauseWork;
use crate::algorithms::closure::{assign_literal, backtrack_to_level, propagate_counting, pseudo_complete};
use crate::algorithms::learning::Analyzer;
use crate::algorithms::closure::Conflict;
use crate::algorithms::lit::{Lit, Reason, Semantics, Value};
use crate::algorithms::node::Node;
use crate::algorithms::stats::Stats;

/// A conflict-driven search for extensions of one framework under one
/// semantics
pub struct Solver<'a> {
    af: &'a AF,
    node: Node,
    analyzer: Analyzer,
    activity: Activity,
    // Scratch space for `decide`: the undecided arguments it popped
    popped: Vec<usize>,
    // Under stable semantics, the arguments by most attackers, then id
    by_most_attackers: Vec<usize>,
    // Each argument's saved phase: the value it last had before
    // backtracking undecided it, Undecided if it never had one
    phase: Vec<Value>,
    save_phases: bool,
    stats: Stats,
    verbose: bool,
    // Whether the arguments nothing attacks have been put in yet. They
    // belong to every extension, and go in with the first call's
    // assumptions at level 0.
    started: bool,
    // The number of conflicts at which the clause database is next reduced
    next_reduction: usize,
    // The number of conflicts at which the search next restarts, how many
    // restarts there have been, which sets the next interval, and the unit
    // the Luby sequence is scaled by
    next_restart: usize,
    restarts: usize,
    restart_unit: usize,
}

// The search restarts after RESTART_UNIT times the Luby sequence's next
// term conflicts: short runs mostly, with ever longer ones in between, so
// that the learned clauses and activities steer fresh descents without
// the search ever being cut off for good.
const RESTART_UNIT: usize = 100;

/// The `i`th term (from 1) of the Luby sequence 1, 1, 2, 1, 1, 2, 4, 1, 1,
/// 2, 1, 1, 2, 4, 8, ...: each block is the sequence so far followed by the
/// next power of two
fn luby(i: usize) -> usize {
    let mut x = i - 1;
    // The smallest complete block (of size 2^(seq+1) - 1) containing x
    let (mut size, mut seq) = (1, 0);
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    // Descend into the half of the block x falls in, until x is its last
    // term, the power of two
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    1 << seq
}

/// The arguments by number of attackers, fewest first or, if `most_first`,
/// most first, and by id among equals: a counting sort, as frameworks can
/// have millions of arguments
fn by_attacker_count(af: &AF, most_first: bool) -> Vec<usize> {
    let n = af.argument_count();
    let max = (0..n).map(|a| af.attacker_count(a)).max().unwrap_or(0);
    // The start of each count's block, in the order the blocks go
    let mut start = vec![0; max + 2];
    for a in 0..n {
        let count = af.attacker_count(a);
        start[if most_first { max - count } else { count } + 1] += 1;
    }
    for i in 1..start.len() {
        start[i] += start[i - 1];
    }
    let mut order = vec![0; n];
    for a in 0..n {
        let count = af.attacker_count(a);
        let block = if most_first { max - count } else { count };
        order[start[block]] = a;
        start[block] += 1;
    }
    order
}

// How many arguments as active as the best defender `decide` pops before
// it turns to scanning the targets' attackers instead
const TIES_POPPED: usize = 16;

// Learned clauses are reduced for the first time after this many
// conflicts, and then after this many more plus REDUCTION_GROWTH per
// reduction so far, so that the database is allowed to grow slowly.
const FIRST_REDUCTION: usize = 2000;
const REDUCTION_GROWTH: usize = 300;
// A clause spanning no more decision levels than this is kept for good: it
// ties few blocks of assignments together, so it keeps becoming unit.
const GLUE_LBD: usize = 2;

impl<'a> Solver<'a> {
    /// A solver for `af` under `semantics`. If `verbose`, it prints its
    /// progress to stderr every thousand conflicts.
    pub fn new(af: &'a AF, semantics: Semantics, verbose: bool) -> Solver<'a> {
        Solver {
            af,
            node: Node::new(af, semantics),
            analyzer: Analyzer::new(af.argument_count()),
            // Equally active arguments come out of the heap as `decide`
            // prefers defenders: fewest attackers first
            activity: Activity::new(by_attacker_count(af, false)),
            popped: Vec::new(),
            by_most_attackers: match semantics {
                Semantics::Complete => Vec::new(),
                Semantics::Stable => by_attacker_count(af, true),
            },
            phase: vec![Value::Undecided; af.argument_count()],
            save_phases: true,
            stats: Stats::default(),
            verbose,
            started: false,
            next_reduction: FIRST_REDUCTION,
            next_restart: RESTART_UNIT * luby(1),
            restarts: 0,
            restart_unit: RESTART_UNIT,
        }
    }

    /// Delete the less promising half of the learned clauses: the ones
    /// spanning the most decision levels, oldest first among equals. Kept
    /// regardless are glue clauses, and the clauses that are the reason
    /// for an assignment on the trail, which analysis may still need.
    fn reduce_clauses(&mut self) {
        let db = self.node.clauses();
        let mut locked = vec![false; db.clause_count()];
        for &lit in self.node.trail() {
            if let Lit::In(a) | Lit::Out(a) = lit
                && let Reason::Clause(idx) = self.node.reason(a)
            {
                locked[idx] = true;
            }
        }
        let mut removable: Vec<(usize, usize)> = (0..db.clause_count())
            .filter(|&idx| db.is_live(idx) && !locked[idx] && db.lbd(idx) > GLUE_LBD && db.clause(idx).len() >= 2)
            .map(|idx| (db.lbd(idx), idx))
            .collect();
        // Worst first: highest LBD, and among equals the oldest
        removable.sort_unstable_by_key(|&(lbd, idx)| (std::cmp::Reverse(lbd), idx));
        removable.truncate(removable.len() / 2);
        let mut doomed = vec![false; db.clause_count()];
        for &(_, idx) in &removable {
            doomed[idx] = true;
        }
        let deleted = self.node.clauses_mut().reduce(|idx, _, _| doomed[idx]);
        self.stats.reductions += 1;
        self.stats.deleted += deleted;
        self.stats.clauses = self.node.clauses().live_count();
    }

    /// The diagnostics gathered so far
    pub fn stats(&self) -> &Stats {
        &self.stats
    }

    /// Reduce the clause database for the first time after `conflicts`
    /// conflicts instead of the default, to exercise reductions on small
    /// frameworks
    #[cfg(test)]
    pub fn set_first_reduction(&mut self, conflicts: usize) {
        self.next_reduction = conflicts;
    }

    /// Restart after every `unit` times the Luby sequence conflicts
    /// instead of the default unit, to exercise restarts on small
    /// frameworks
    #[cfg(test)]
    pub fn set_restart_unit(&mut self, unit: usize) {
        self.restart_unit = unit;
        self.next_restart = unit * luby(1);
    }

    /// Decide every argument in once no target is left, instead of by its
    /// saved phase, as a reference for testing phase saving
    #[cfg(test)]
    pub fn set_phase_saving(&mut self, on: bool) {
        self.save_phases = on;
    }

    /// Find an extension that contains `assumptions` -- and everything
    /// assumed in earlier calls, since the clauses learned since then are
    /// only known to hold for extensions containing those. Returns `None`
    /// if there is no such extension.
    pub fn solve(&mut self, assumptions: &[usize]) -> Option<HashSet<usize>> {
        let af = self.af;
        let started_at = Instant::now();
        self.backtrack(0);

        let mut seeds = assumptions.to_vec();
        if !self.started {
            self.started = true;
            seeds.extend((0..af.argument_count()).filter(|&a| af.attacker_count(a) == 0));
        }
        self.stats.propagations += 1;
        let mut result = pseudo_complete(seeds, &mut self.node, af);

        loop {
            match result {
                Err(conflict) => {
                    let started = Instant::now();
                    let learned = self.analyzer.analyze(conflict, &self.node, af, &mut self.activity)
                        .expect("decisions are only made on undecided arguments");
                    self.activity.decay();
                    self.stats.analysing += started.elapsed();
                    self.stats.record_learned(&learned, self.node.decision_level());
                    if self.verbose && self.stats.conflicts.is_multiple_of(1000) {
                        eprintln!(
                            "[progress] t={:.1}s {} level={}",
                            started_at.elapsed().as_secs_f64(),
                            self.stats,
                            self.node.decision_level()
                        );
                    }
                    if learned.literals.is_empty() {
                        // Contradictory at level 0: the assumptions
                        // themselves rule out every extension.
                        return None;
                    }
                    // Back to where the clause has exactly one literal not
                    // yet false, and make that one true. A unit clause has
                    // no watches, and its literal, asserted at level 0, is
                    // never undone. Now and then the search restarts
                    // instead, back to level 0 for a fresh descent under
                    // the activities and clauses learned since. The clause
                    // is then only stored: its other literals are no longer
                    // false, so it justifies nothing yet, and its watches
                    // will catch it when it becomes unit again.
                    let started = Instant::now();
                    let restart = self.stats.conflicts >= self.next_restart
                        && learned.assertion_level > 0;
                    if restart {
                        self.restarts += 1;
                        self.stats.restarts = self.restarts;
                        self.next_restart = self.stats.conflicts + self.restart_unit * luby(self.restarts + 1);
                    }
                    let level = if restart { 0 } else { learned.assertion_level };
                    self.backtrack(level);
                    self.stats.backtracking += started.elapsed();
                    let first = learned.literals[0];
                    let idx = self.node.clauses_mut().add_clause(learned.literals, learned.lbd);
                    self.stats.clauses = self.node.clauses().live_count();
                    result = if restart {
                        Ok(())
                    } else {
                        assign_literal(first, Reason::Clause(idx), &mut self.node)
                            .and_then(|()| self.propagate())
                    };
                }
                Ok(()) => {
                    #[cfg(test)]
                    self.node.check_clauses();
                    #[cfg(test)]
                    self.node.check_targets();
                    if self.stats.conflicts >= self.next_reduction {
                        self.reduce_clauses();
                        #[cfg(test)]
                        self.node.check_clauses();
                        self.next_reduction = self.stats.conflicts
                            + FIRST_REDUCTION
                            + REDUCTION_GROWTH * self.stats.reductions;
                    }
                    let started = Instant::now();
                    let decision = self.decide();
                    self.stats.deciding += started.elapsed();
                    let Some(lit) = decision else {
                        return Some(self.node.arguments());
                    };
                    self.stats.decisions += 1;
                    if let Lit::Out(_) = lit {
                        self.stats.out_decisions += 1;
                    }
                    self.node.new_level();
                    result = assign_literal(lit, Reason::Decision, &mut self.node)
                        .and_then(|()| self.propagate());
                }
            }
        }
    }

    /// Propagate what is queued on the trail, timing it and counting what
    /// the learned clauses cost
    fn propagate(&mut self) -> Result<(), Conflict> {
        self.stats.propagations += 1;
        let started = Instant::now();
        let mut work = ClauseWork::default();
        let result = propagate_counting(&mut self.node, self.af, &mut work);
        self.stats.propagating += started.elapsed();
        self.stats.clause_visits += work.visits;
        self.stats.clause_literals_scanned += work.literals_scanned;
        result
    }

    /// The next decision, or `None` if the assignment already is an
    /// extension.
    ///
    /// The targets are the arguments that must be defeated but are not yet
    /// attacked by the set: under complete semantics the undefeated
    /// attackers of members, under stable semantics also every argument
    /// that is out. While there are targets, the decision puts a usable
    /// defender of one of them in; see `choose_defender`.
    ///
    /// Under stable semantics, once no target is left, an argument that is
    /// still undecided has to be either in or attacked. The choice is the
    /// most active one, and among equals the one with the most attackers:
    /// the one most likely to fail in, so that what it fails on is learned
    /// early. (Measured on the ICCMA'25 stable samples; fewest attackers
    /// first was worse.) It gets its saved phase, the value it had before
    /// the search last backtracked over it, and is put in if it never had
    /// one: a restart or backjump then rebuilds the part of the extension
    /// that did not take part in the conflict, as SAT solvers' phase saving
    /// does. (On SE-ST st_542, 562s without phases, 60s with. Saving the
    /// phases of defenders too was much worse: most decisions turned out.)
    fn decide(&mut self) -> Option<Lit> {
        if self.node.targets().is_empty() {
            return match self.node.semantics() {
                Semantics::Complete => None,
                Semantics::Stable => self.most_active_undecided().map(|a| match self.phase[a] {
                    Value::Out if self.save_phases => Lit::Out(a),
                    _ => Lit::In(a),
                }),
            };
        }
        Some(Lit::In(self.choose_defender()))
    }

    /// The defender to put in: the most active usable defender of some
    /// target, so that the search stays with the arguments its recent
    /// conflicts were about and the clauses it learns tie few decision
    /// levels together. Among equally active defenders -- all of them,
    /// until the first conflict -- the structural choice decides: the most
    /// constrained target, the one with the fewest usable defenders, and
    /// its defender with the fewest attackers of its own, hence the least
    /// likely to need defending in turn. Ties go to the smaller id, so that
    /// the search does not depend on how the framework is stored.
    ///
    /// The heap hands out arguments most active first, so the search pops
    /// until it finds a defender, and goes on through the arguments just as
    /// active, each looked at by a scan of its victims. The heap orders
    /// equals as defenders are preferred, fewest attackers first, so a
    /// defender of a target with only two usable defenders, the fewest
    /// there can be, ends the search at once. When the equally active
    /// arguments are many -- typically those never involved in a conflict
    /// -- the targets' attackers are scanned instead. Arguments popped
    /// while undecided go back in, the decided ones return to the heap
    /// when backtracking undecides them.
    fn choose_defender(&mut self) -> usize {
        let node = &self.node;
        let af = self.af;
        // (usable defenders of its target, attackers, id) of the best
        // defender so far, the lowest being best, and its activity
        let mut best: Option<(usize, usize, usize)> = None;
        let mut best_activity = 0.0;
        let mut ties = 0;
        let mut ties_left = false;
        let mut popped = std::mem::take(&mut self.popped);
        let (mut pops, mut victims) = (0, 0);
        while let Some(c) = self.activity.pop() {
            pops += 1;
            if node.value(c) != Value::Undecided {
                continue;
            }
            popped.push(c);
            if best.is_some() {
                if self.activity.of(c) < best_activity {
                    break;
                }
                ties += 1;
                if ties > TIES_POPPED {
                    ties_left = true;
                    break;
                }
            }
            // The most constrained target `c` defends against. The count
            // is maintained by the closure, so a read rather than a scan;
            // after propagation it is exact and at least two: with fewer
            // the closure would have forced the defender or failed.
            victims += af.victims(c).len();
            let count = af.victims(c)
                .filter(|&&b| node.known_defeated(b) && !node.defeat_propagated(b))
                .map(|&b| node.usable_defenders_count(b))
                .min();
            if let Some(count) = count {
                let key = (count, af.attacker_count(c), c);
                if best.is_none_or(|best| key < best) {
                    best = Some(key);
                    best_activity = self.activity.of(c);
                }
                // No count is lower, and the equally active arguments
                // still to come rank behind `c` on the rest of the key
                if count == 2 {
                    break;
                }
            }
        }
        self.stats.heap_pops += pops;
        self.stats.heap_undecided += popped.len();
        self.stats.victims_scanned += victims;
        for &c in &popped {
            self.activity.insert(c);
        }
        popped.clear();
        self.popped = popped;
        // Every target has at least two usable defenders, all undecided,
        // and every undecided argument is in the heap
        let mut best = best.expect("a target has an undecided attacker");
        if ties_left {
            for &b in node.targets() {
                let count = node.usable_defenders_count(b);
                if count > best.0 {
                    continue;
                }
                self.stats.victims_scanned += af.attacker_count(b);
                for &c in af.attackers(b) {
                    if node.value(c) == Value::Undecided && self.activity.of(c) == best_activity {
                        best = best.min((count, af.attacker_count(c), c));
                    }
                }
            }
        }
        best.2
    }

    /// Under stable semantics, once no target is left: the most active
    /// undecided argument, among equals the one with the most attackers,
    /// then the smallest id. The heap yields equals by fewest attackers,
    /// so all of the most active ones are popped to find it -- unless
    /// they are inactive, never involved in a conflict.
    fn most_active_undecided(&mut self) -> Option<usize> {
        if self.node.undecided_count() == 0 {
            return None;
        }
        let node = &self.node;
        let af = self.af;
        let mut best: Option<usize> = None;
        let mut popped = std::mem::take(&mut self.popped);
        while let Some(c) = self.activity.pop() {
            self.stats.heap_pops += 1;
            if node.value(c) != Value::Undecided {
                continue;
            }
            popped.push(c);
            match best {
                // Then every undecided argument is as inactive, and the
                // order they are wanted in is known in advance
                None if self.activity.of(c) == 0.0 => {
                    best = self.by_most_attackers.iter().copied().find(|&a| node.value(a) == Value::Undecided);
                    break;
                }
                None => best = Some(c),
                Some(b) if self.activity.of(c) < self.activity.of(b) => break,
                Some(b) if af.attacker_count(c) > af.attacker_count(b) => best = Some(c),
                Some(_) => {}
            }
        }
        self.stats.heap_undecided += popped.len();
        for &c in &popped {
            self.activity.insert(c);
        }
        popped.clear();
        self.popped = popped;
        best
    }

    /// Backtrack to `level`, putting the arguments that become undecided
    /// back into the activity heap
    fn backtrack(&mut self, level: usize) {
        let keep = self.node.trail_len_at(level);
        for &lit in &self.node.trail()[keep..] {
            match lit {
                Lit::In(a) => {
                    self.activity.insert(a);
                    self.phase[a] = Value::In;
                }
                Lit::Out(a) => {
                    self.activity.insert(a);
                    self.phase[a] = Value::Out;
                }
                Lit::Def(_) => {}
            }
        }
        backtrack_to_level(level, &mut self.node, self.af);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::random_af::{random_af, Rng};

    #[test]
    fn test_by_attacker_count() {
        let mut rng = Rng::new(5);
        for _ in 0..50 {
            let n = 1 + rng.below(20);
            let af = random_af(&mut rng, n, 30);
            let mut fewest: Vec<usize> = (0..af.argument_count()).collect();
            fewest.sort_by_key(|&a| (af.attacker_count(a), a));
            assert_eq!(by_attacker_count(&af, false), fewest);
            let mut most: Vec<usize> = (0..af.argument_count()).collect();
            most.sort_by_key(|&a| (std::cmp::Reverse(af.attacker_count(a)), a));
            assert_eq!(by_attacker_count(&af, true), most);
        }
    }

    #[test]
    fn test_luby() {
        let terms: Vec<usize> = (1..=16).map(luby).collect();
        assert_eq!(terms, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1]);
    }

    // Restarting as early as the search allows, and reducing the clause
    // database every few conflicts, must not change any answer: on random
    // small frameworks the solver so configured agrees with brute force,
    // under both semantics. Restarts stay rare here -- the closure settles
    // tiny frameworks at level 1, where a restart is just the backjump --
    // so the differential test below is what exercises them in numbers.
    #[test]
    fn test_restarts_and_reductions_match_brute_force() {
        let mut rng = Rng::new(10);
        let mut restarts = 0;
        for round in 0..1500 {
            let n = 2 + rng.below(12);
            let percent = [10, 20, 35, 50][rng.below(4)];
            let af = random_af(&mut rng, n, percent);
            let subsets: Vec<HashSet<usize>> = (0..1u32 << n)
                .map(|bits| (0..n).filter(|&a| bits & (1 << a) != 0).collect())
                .collect();
            for semantics in [Semantics::Complete, Semantics::Stable] {
                let valid = |set: &HashSet<usize>| match semantics {
                    Semantics::Complete => af.is_complete(set),
                    Semantics::Stable => af.is_stable(set),
                };
                let extensions: Vec<&HashSet<usize>> = subsets.iter().filter(|set| valid(set)).collect();
                for query in 0..n {
                    let expected = extensions.iter().any(|set| set.contains(&query));
                    let mut solver = Solver::new(&af, semantics, false);
                    solver.set_restart_unit(1 + rng.below(2));
                    solver.set_first_reduction(3);
                    let answer = solver.solve(&[query]);
                    restarts += solver.stats().restarts;
                    match answer {
                        Some(extension) => {
                            assert!(expected, "round {round}, {semantics:?}, query {query}: YES wrongly\n{af}");
                            assert!(extension.contains(&query) && valid(&extension),
                                "round {round}, {semantics:?}, query {query}: {extension:?}\n{af}");
                        }
                        None => assert!(!expected, "round {round}, {semantics:?}, query {query}: NO wrongly\n{af}"),
                    }
                }
            }
        }
        // Often none at all: fine, the configuration is what is under test
        let _ = restarts;
    }

    // Under stable semantics, an argument decided once no target is left
    // gets its saved phase, so after a backjump or restart it may be
    // decided out. That happens mostly to an argument that was out by
    // propagation, the other half of a mutual attack, so the frameworks
    // here pair up all arguments in mutual attacks and add sparse random
    // ones. The answers agree with the same search deciding every such
    // argument in. One solver answers a
    // growing list of assumptions, so phases and clauses carry over
    // between calls.
    #[test]
    fn test_saved_phases_keep_answers() {
        let mut rng = Rng::new(11);
        let mut out_decisions = 0;
        let mut answers = [0, 0];
        for round in 0..200 {
            let n = 40 + rng.below(121);
            let percent = [1, 2, 3][rng.below(3)];
            let mut af = random_af(&mut rng, n, percent);
            for a in (0..n - 1).step_by(2) {
                af.add_attack(a, a + 1);
                af.add_attack(a + 1, a);
            }
            let mut saving = Solver::new(&af, Semantics::Stable, false);
            saving.set_restart_unit(1);
            let mut plain = Solver::new(&af, Semantics::Stable, false);
            plain.set_phase_saving(false);
            let mut assumed = Vec::new();
            for _ in 0..5 {
                assumed.push(rng.below(n));
                let answer = saving.solve(&assumed);
                let expected = plain.solve(&assumed);
                assert_eq!(answer.is_some(), expected.is_some(),
                    "round {round}, {assumed:?}: {answer:?} vs {expected:?}\n{af}");
                match answer {
                    Some(extension) => {
                        assert!(assumed.iter().all(|a| extension.contains(a)) && af.is_stable(&extension),
                            "round {round}, {assumed:?}: {extension:?}\n{af}");
                        answers[0] += 1;
                    }
                    None => {
                        answers[1] += 1;
                        break;
                    }
                }
            }
            out_decisions += saving.stats().out_decisions;
        }
        assert!(out_decisions > 500, "too few decisions put an argument out ({out_decisions})");
        assert!(answers[0] > 100 && answers[1] > 50, "answers too one-sided: {answers:?}");
    }

    // Deleting learned clauses and restarting change what the search does,
    // but not what it answers: with the database reduced every few
    // conflicts and a restart at every opportunity the solver agrees with
    // itself unreduced and never restarting, on random frameworks dense
    // enough for searches to have many conflicts at depth.
    #[test]
    fn test_reductions_and_restarts_keep_answers() {
        let mut rng = Rng::new(9);
        let mut reductions = 0;
        let mut restarts = 0;
        let mut conflicts = 0;
        let mut answers = [0, 0];
        for round in 0..120 {
            let n = 60 + rng.below(61);
            let percent = [10, 15][rng.below(2)];
            let af = random_af(&mut rng, n, percent);
            let query = rng.below(n);
            for semantics in [Semantics::Complete, Semantics::Stable] {
                let mut plain = Solver::new(&af, semantics, false);
                plain.set_restart_unit(usize::MAX / 1024);
                let expected = plain.solve(&[query]);
                let mut reducing = Solver::new(&af, semantics, false);
                reducing.set_first_reduction(5);
                reducing.set_restart_unit(1);
                let answer = reducing.solve(&[query]);
                assert_eq!(answer.is_some(), expected.is_some(),
                    "round {round}, {semantics:?}, query {query}: reduced {answer:?} vs {expected:?}\n{af}");
                if let Some(extension) = &answer {
                    let valid = match semantics {
                        Semantics::Complete => af.is_complete(extension),
                        Semantics::Stable => af.is_stable(extension),
                    };
                    assert!(valid && extension.contains(&query), "round {round}: {extension:?}\n{af}");
                    answers[0] += 1;
                } else {
                    answers[1] += 1;
                }
                reductions += reducing.stats().reductions;
                restarts += reducing.stats().restarts;
                conflicts += reducing.stats().conflicts;
            }
        }
        assert!(reductions > 50, "too few reductions ({reductions}) to mean much");
        assert!(restarts > 100, "too few restarts ({restarts}) to mean much");
        assert!(conflicts > 2000, "too few conflicts ({conflicts}) to mean much");
        // Random frameworks this dense refute most queries, so YES is rare
        assert!(answers[0] >= 5 && answers[1] > 50, "answers too one-sided: {answers:?}");
    }
}
