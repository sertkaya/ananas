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
    stats: Stats,
    verbose: bool,
    // Whether the arguments nothing attacks have been put in yet. They
    // belong to every extension, and go in with the first call's
    // assumptions at level 0.
    started: bool,
    // The number of conflicts at which the clause database is next reduced
    next_reduction: usize,
}

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
            stats: Stats::default(),
            verbose,
            started: false,
            next_reduction: FIRST_REDUCTION,
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

    /// Find an extension that contains `assumptions` -- and everything
    /// assumed in earlier calls, since the clauses learned since then are
    /// only known to hold for extensions containing those. Returns `None`
    /// if there is no such extension.
    pub fn solve(&mut self, assumptions: &[usize]) -> Option<HashSet<usize>> {
        let af = self.af;
        let started_at = Instant::now();
        backtrack_to_level(0, &mut self.node, af);

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
                    let learned = self.analyzer.analyze(conflict, &self.node, af)
                        .expect("decisions are only made on undecided arguments");
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
                    // never undone.
                    let started = Instant::now();
                    backtrack_to_level(learned.assertion_level, &mut self.node, af);
                    self.stats.backtracking += started.elapsed();
                    let first = learned.literals[0];
                    let idx = self.node.clauses_mut().add_clause(learned.literals, learned.lbd);
                    self.stats.clauses = self.node.clauses().live_count();
                    result = assign_literal(first, Reason::Clause(idx), &mut self.node)
                        .and_then(|()| self.propagate());
                }
                Ok(()) => {
                    #[cfg(test)]
                    self.node.check_clauses();
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
                    let Some(c) = decision else {
                        return Some(self.node.arguments());
                    };
                    self.stats.decisions += 1;
                    self.node.new_level();
                    result = assign_literal(Lit::In(c), Reason::Decision, &mut self.node)
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

    /// The next argument to put in, or `None` if the assignment already is
    /// an extension.
    ///
    /// The targets are the arguments that must be defeated but are not yet
    /// attacked by the set: under complete semantics the undefeated
    /// attackers of members, under stable semantics also every argument
    /// that is out. The decision defends against the most constrained
    /// target -- the one with the fewest usable defenders -- with the
    /// defender that has the fewest attackers of its own, hence is the
    /// least likely to need defending in turn. Ties go to the smaller id,
    /// so that the search does not depend on how the framework is stored.
    ///
    /// Under stable semantics, once no target is left, an argument that is
    /// still undecided has to be either in or attacked, so it is decided in
    /// -- and learned out if that fails.
    fn decide(&self) -> Option<usize> {
        let node = &self.node;
        let af = self.af;
        let mut best: Option<(usize, usize)> = None;
        for b in 0..af.argument_count() {
            if !node.known_defeated(b) || node.defeat_propagated(b) {
                continue;
            }
            // Maintained by the closure, so a read rather than a scan
            let count = node.usable_defenders_count(b);
            if best.is_none_or(|(best_count, best_b)| (count, b) < (best_count, best_b)) {
                best = Some((count, b));
            }
        }
        if let Some((_, b)) = best {
            // After propagation the count is exact and at least two: with
            // fewer the closure would have forced the defender or failed.
            let c = af.attackers(b)
                .copied()
                .filter(|&c| node.value(c) == Value::Undecided)
                .min_by_key(|&c| (af.attacker_count(c), c))
                .expect("a target with fewer than two usable defenders is resolved by the closure");
            return Some(c);
        }
        match node.semantics() {
            Semantics::Complete => None,
            Semantics::Stable => (0..af.argument_count()).find(|&a| node.value(a) == Value::Undecided),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::random_af::{random_af, Rng};

    // Deleting learned clauses changes what the search does, but not what
    // it answers: with the database reduced every few conflicts the solver
    // agrees with itself unreduced, on random frameworks large enough for
    // searches to have many conflicts.
    #[test]
    fn test_reduction_keeps_answers() {
        let mut rng = Rng::new(9);
        let mut reductions = 0;
        let mut conflicts = 0;
        let mut answers = [0, 0];
        for round in 0..120 {
            let n = 60 + rng.below(61);
            let percent = [10, 15][rng.below(2)];
            let af = random_af(&mut rng, n, percent);
            let query = rng.below(n);
            for semantics in [Semantics::Complete, Semantics::Stable] {
                let mut plain = Solver::new(&af, semantics, false);
                let expected = plain.solve(&[query]);
                let mut reducing = Solver::new(&af, semantics, false);
                reducing.set_first_reduction(5);
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
                conflicts += reducing.stats().conflicts;
            }
        }
        assert!(reductions > 50, "too few reductions ({reductions}) to mean much");
        assert!(conflicts > 2000, "too few conflicts ({conflicts}) to mean much");
        // Random frameworks this dense refute most queries, so YES is rare
        assert!(answers[0] >= 5 && answers[1] > 50, "answers too one-sided: {answers:?}");
    }
}
