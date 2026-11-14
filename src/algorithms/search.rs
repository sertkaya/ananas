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
use crate::af::AF;
use crate::algorithms::closure::{assign_literal, backtrack_to_level, propagate, pseudo_complete};
use crate::algorithms::learning::Analyzer;
use crate::algorithms::lit::{Reason, Semantics, Value};
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
}

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
        }
    }

    /// The diagnostics gathered so far
    pub fn stats(&self) -> &Stats {
        &self.stats
    }

    /// Find an extension that contains `assumptions` -- and everything
    /// assumed in earlier calls, since the clauses learned since then are
    /// only known to hold for extensions containing those. Returns `None`
    /// if there is no such extension.
    pub fn solve(&mut self, assumptions: &[usize]) -> Option<HashSet<usize>> {
        let af = self.af;
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
                    let learned = self.analyzer.analyze(conflict, &self.node, af)
                        .expect("decisions are only made on undecided arguments");
                    self.stats.record_learned(&learned, self.node.decision_level());
                    if self.verbose && self.stats.conflicts.is_multiple_of(1000) {
                        eprintln!("[progress] {} level={}", self.stats, self.node.decision_level());
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
                    backtrack_to_level(learned.assertion_level, &mut self.node, af);
                    let first = learned.literals[0];
                    let idx = self.node.clauses_mut().add_clause(learned.literals);
                    self.stats.clauses = self.node.clauses().clause_count();
                    self.stats.propagations += 1;
                    result = assign_literal(first, Reason::Clause(idx), &mut self.node)
                        .and_then(|()| propagate(&mut self.node, af));
                }
                Ok(()) => {
                    #[cfg(test)]
                    self.node.check_clauses();
                    let Some(c) = self.decide() else {
                        return Some(self.node.arguments());
                    };
                    self.stats.decisions += 1;
                    self.node.new_level();
                    self.stats.propagations += 1;
                    result = pseudo_complete(vec![c], &mut self.node, af);
                }
            }
        }
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
