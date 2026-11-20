//! Conflict analysis: from a conflict that propagation ran into, derive a
//! clause over in/out literals that every complete extension containing
//! the query satisfies, and that rules out the assignment that caused it.
//!
//! The implication graph has two kinds of node, `In`/`Out` literals and
//! `Def` literals. Every `Def(b)` has exactly one antecedent -- the member
//! that `b` attacks or is attacked by, recorded as its def source -- so a
//! `Def` antecedent is always resolved away into that member's `In`
//! literal on the spot. Learned clauses therefore contain only in/out
//! literals, and can only ever force an argument in or out.

use crate::af::AF;
use crate::algorithms::activity::Activity;
use crate::algorithms::closure::Conflict;
use crate::algorithms::lit::{Lit, Reason, Value};
use crate::algorithms::node::Node;

/// A clause learned from a conflict: a disjunction of in/out literals that
/// every complete extension containing the query satisfies, and that is
/// false under the assignment the conflict arose in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Learned {
    /// The literals. The first is the negated first unique implication
    /// point, the only literal at the conflict's decision level -- unless
    /// more than one argument was assumed at that level, since an
    /// assumption has no antecedents to resolve and keeps its literal.
    pub literals: Vec<Lit>,
    /// The highest decision level among the literals after the first:
    /// backjumping there leaves the first as the only one not yet false.
    /// 0 for a unit clause.
    pub assertion_level: usize,
    /// How many literals the clause had before minimization removed the
    /// ones implied by the others
    pub unminimized_len: usize,
    /// The literal block distance: how many distinct decision levels the
    /// literals were assigned at. Literals from one level were propagated
    /// together from one decision and tend to recur together, so the fewer
    /// levels a clause spans, the sooner it is likely to become unit again.
    pub lbd: usize,
}

/// The literal that held when `b` became known defeated, standing in for
/// `Def(b)` itself
fn def_antecedent(b: usize, node: &Node) -> Lit {
    node.def_source(b)
}

/// Push to `out` the literals that implied giving `arg` a value for
/// `reason`, all true when it was given. Returns `false`, pushing nothing,
/// for an assumption, which has none.
fn antecedents(arg: usize, reason: Reason, node: &Node, af: &AF, out: &mut Vec<Lit>) -> bool {
    match reason {
        Reason::Decision => return false,
        // Out from the start, at level 0, so never part of a clause
        Reason::SelfAttack => {}
        Reason::Member(m) => out.push(Lit::In(m)),
        Reason::Completeness => {
            out.extend(af.attackers(arg).map(|&b| def_antecedent(b, node)));
        }
        Reason::OnlyDefender(b) => {
            out.push(def_antecedent(b, node));
            out.extend(af.attackers(b).filter(|&&c| c != arg).map(|&c| Lit::Out(c)));
        }
        Reason::Clause(idx) => {
            out.extend(
                node.clauses().clause(idx).iter().filter(|&&l| l.arg() != arg).map(|&l| l.negated()),
            );
        }
    }
    true
}

/// The literals that are true and together contradict each other in
/// `conflict`, or `None` if the conflict was an assumption contradicting
/// the assignment outright, which no clause can explain.
fn conflict_literals(conflict: Conflict, node: &Node, af: &AF) -> Option<Vec<Lit>> {
    let mut lits = Vec::new();
    match conflict {
        Conflict::Clash { arg, reason } => {
            if !antecedents(arg, reason, node, af, &mut lits) {
                return None;
            }
            lits.push(match node.value(arg) {
                Value::In => Lit::In(arg),
                Value::Out => Lit::Out(arg),
                Value::Undecided => unreachable!("a clash is with a decided argument"),
            });
        }
        Conflict::NoDefender(b) => {
            lits.push(def_antecedent(b, node));
            lits.extend(af.attackers(b).map(|&c| Lit::Out(c)));
        }
        Conflict::Clause(idx) => {
            lits.extend(node.clauses().clause(idx).iter().map(|&l| l.negated()));
        }
    }
    Some(lits)
}

/// Conflict analysis, with its working memory kept between conflicts
pub struct Analyzer {
    // Arguments already accounted for in the clause being built, either as
    // one of its literals or resolved away through their antecedents
    seen: Vec<bool>,
    // The arguments marked seen, to unmark them afterwards
    touched: Vec<usize>,
    // Scratch space for antecedents, and for the redundancy check's
    // depth-first walk
    buffer: Vec<Lit>,
    stack: Vec<usize>,
    // Stamps per decision level for counting a clause's distinct levels,
    // and the ones stamped, to clear them afterwards
    level_seen: Vec<bool>,
    levels_touched: Vec<usize>,
}

impl Analyzer {
    /// An analyzer for a framework of `argument_count` arguments
    pub fn new(argument_count: usize) -> Analyzer {
        Analyzer {
            seen: vec![false; argument_count],
            touched: Vec::new(),
            buffer: Vec::new(),
            stack: Vec::new(),
            // There can be no more decision levels than arguments
            level_seen: vec![false; argument_count + 1],
            levels_touched: Vec::new(),
        }
    }

    /// Mark the argument of `lit` seen, bumping its activity. Returns 1 if
    /// that puts `lit` among the literals still to resolve at the conflict
    /// level, 0 if it was already seen, holds at level 0, or went into the
    /// clause.
    fn mark(&mut self, lit: Lit, level: usize, node: &Node, literals: &mut Vec<Lit>, activity: &mut Activity) -> usize {
        let a = lit.arg();
        let lit_level = node.level(a);
        if lit_level == 0 || self.seen[a] {
            return 0;
        }
        self.seen[a] = true;
        self.touched.push(a);
        activity.bump(a);
        if lit_level == level {
            1
        } else {
            literals.push(lit.negated());
            0
        }
    }

    /// Whether the assignment of `a` follows from assignments already seen
    /// -- the clause's other literals and what they implied -- so that the
    /// clause's literal about `a` is redundant. `abstract_levels` has a bit
    /// set for each level the clause has literals at; an assignment at any
    /// other level cannot follow, since it has an antecedent at its own
    /// level and that level's decision is not seen.
    ///
    /// Everything the walk marks seen on success stays seen, being implied
    /// by the clause as well; on failure the marks are taken back.
    fn redundant(&mut self, a: usize, abstract_levels: u64, node: &Node, af: &AF) -> bool {
        let marked_before = self.touched.len();
        self.stack.clear();
        self.stack.push(a);
        while let Some(x) = self.stack.pop() {
            let mut buffer = std::mem::take(&mut self.buffer);
            buffer.clear();
            let explained = antecedents(x, node.reason(x), node, af, &mut buffer);
            let mut failed = !explained;
            if explained {
                for &lit in &buffer {
                    let y = lit.arg();
                    let y_level = node.level(y);
                    if y_level == 0 || self.seen[y] {
                        continue;
                    }
                    let assumed = node.reason(y) == Reason::Decision;
                    if assumed || abstract_levels & (1 << (y_level % 64)) == 0 {
                        failed = true;
                        break;
                    }
                    self.seen[y] = true;
                    self.touched.push(y);
                    self.stack.push(y);
                }
            }
            self.buffer = buffer;
            if failed {
                for &y in &self.touched[marked_before..] {
                    self.seen[y] = false;
                }
                self.touched.truncate(marked_before);
                return false;
            }
        }
        true
    }

    /// How many distinct decision levels the literals of `clause` are
    /// assigned at. The touched-marks are free at this point, so they
    /// serve as the level stamps.
    fn distinct_levels(&mut self, clause: &[Lit], node: &Node) -> usize {
        let mut count = 0;
        for &lit in clause {
            let level = node.level(lit.arg());
            if !self.level_seen[level] {
                self.level_seen[level] = true;
                self.levels_touched.push(level);
                count += 1;
            }
        }
        for &level in &self.levels_touched {
            self.level_seen[level] = false;
        }
        self.levels_touched.clear();
        count
    }

    /// Derive a learned clause from `conflict`, which propagation has just
    /// run into on `node` and which has not been backtracked yet, bumping
    /// the activity of every argument resolved through.
    ///
    /// Resolves the conflict back along the trail, through the antecedents
    /// of each literal at the conflict's decision level, until a single
    /// literal at that level is left -- the first unique implication point.
    /// Literals from level 0 are dropped: they hold in every complete
    /// extension containing the query. A conflict at level 0 gives the
    /// empty clause: no complete extension contains the query. The clause
    /// is then minimized by dropping every literal that the others imply.
    ///
    /// Returns `None` if the conflict was an assumption above level 0
    /// contradicting the assignment outright, which no clause can explain.
    /// At level 0 the assumptions are the query and what follows from the
    /// framework alone, so a contradiction among them gives the empty
    /// clause.
    pub fn analyze(&mut self, conflict: Conflict, node: &Node, af: &AF, activity: &mut Activity) -> Option<Learned> {
        let Some(conflict_lits) = conflict_literals(conflict, node, af) else {
            return (node.decision_level() == 0).then(|| Learned {
                literals: Vec::new(),
                assertion_level: 0,
                unminimized_len: 0,
                lbd: 0,
            });
        };
        let level = conflict_lits.iter().map(|&l| node.level(l.arg())).max().unwrap_or(0);
        if level == 0 {
            return Some(Learned { literals: Vec::new(), assertion_level: 0, unminimized_len: 0, lbd: 0 });
        }

        // Literals from below the conflict level go straight into the
        // clause, negated; the ones at it are counted, and resolved away in
        // reverse trail order until one is left.
        let mut literals: Vec<Lit> = Vec::new();
        let mut pending = 0;
        for lit in conflict_lits {
            pending += self.mark(lit, level, node, &mut literals, activity);
        }

        let trail = node.trail();
        let mut i = trail.len();
        let uip = loop {
            i -= 1;
            let lit = trail[i];
            let a = match lit {
                Lit::In(a) | Lit::Out(a) => a,
                Lit::Def(_) => continue,
            };
            if node.level(a) != level || !self.seen[a] {
                continue;
            }
            pending -= 1;
            if pending == 0 {
                break lit;
            }
            let mut buffer = std::mem::take(&mut self.buffer);
            buffer.clear();
            if antecedents(a, node.reason(a), node, af, &mut buffer) {
                for &antecedent in &buffer {
                    pending += self.mark(antecedent, level, node, &mut literals, activity);
                }
            } else {
                // A further assumption at the conflict level: nothing to
                // resolve it with, so it stays.
                literals.push(lit.negated());
            }
            self.buffer = buffer;
        };

        // Minimize: drop every literal whose assignment the others imply.
        let unminimized_len = literals.len() + 1;
        let abstract_levels = literals.iter()
            .fold(0u64, |bits, &l| bits | 1 << (node.level(l.arg()) % 64));
        let mut kept = Vec::with_capacity(literals.len() + 1);
        kept.push(uip.negated());
        for lit in literals {
            if !self.redundant(lit.arg(), abstract_levels, node, af) {
                kept.push(lit);
            }
        }

        for &a in &self.touched {
            self.seen[a] = false;
        }
        self.touched.clear();

        // The literal from the highest level after the first goes second,
        // to be the clause's other watched literal: it is the last to be
        // undone when the search backtracks, so as long as it is false the
        // first literal is the only one that can be undecided. With any
        // other literal watched instead, the clause could become unit
        // again, below the assertion level, with no watch to notice.
        if kept.len() > 2 {
            let deepest = (1..kept.len())
                .max_by_key(|&i| node.level(kept[i].arg()))
                .expect("at least two literals");
            kept.swap(1, deepest);
        }
        let assertion_level = kept.get(1).map_or(0, |&l| node.level(l.arg()));
        let lbd = self.distinct_levels(&kept, node);
        Some(Learned { literals: kept, assertion_level, unminimized_len, lbd })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use crate::algorithms::closure::{assign_literal, backtrack_to_level, propagate, pseudo_complete};
    use crate::algorithms::complete::dc_co;
    use crate::algorithms::lit::Semantics;

    /// Assume `arg` out, as the search's clauses may make it, and propagate
    fn assume_out(arg: usize, node: &mut Node, af: &AF) -> Result<(), Conflict> {
        assign_literal(Lit::Out(arg), Reason::Decision, node)?;
        propagate(node, af)
    }
    use crate::algorithms::random_af::{random_af, Rng};

    fn analyze(conflict: Conflict, node: &Node, af: &AF) -> Option<Learned> {
        let mut activity = Activity::new((0..af.argument_count()).collect());
        Analyzer::new(af.argument_count()).analyze(conflict, node, af, &mut activity)
    }

    /// Whether the extension `set` satisfies the clause `literals`
    fn satisfies(set: &HashSet<usize>, literals: &[Lit]) -> bool {
        literals.iter().any(|&lit| match lit {
            Lit::In(a) => set.contains(&a),
            Lit::Out(a) => !set.contains(&a),
            Lit::Def(_) => unreachable!("learned clauses have no Def literals"),
        })
    }

    /// Every complete extension of `af` containing `query`, by brute force
    fn extensions_containing(af: &AF, query: usize) -> Vec<HashSet<usize>> {
        let n = af.argument_count();
        (0..1u32 << n)
            .map(|bits| (0..n).filter(|&a| bits & (1 << a) != 0).collect())
            .filter(|set: &HashSet<usize>| set.contains(&query) && af.is_complete(set))
            .collect()
    }

    /// A node with `query` and the unattacked arguments assumed in at
    /// level 0, the way dc_co starts, and the outcome of closing it
    fn root(af: &AF, query: usize) -> (Node, Result<(), Conflict>) {
        let mut node = Node::new(af, Semantics::Complete);
        let mut seeds = vec![query];
        seeds.extend((0..af.argument_count()).filter(|&a| af.attacker_count(a) == 0));
        let result = pseudo_complete(seeds, &mut node, af);
        (node, result)
    }

    /// Whether assuming every literal of `literals` false, on top of the
    /// root closure for `query`, makes propagation run into a conflict --
    /// reverse unit propagation, which a clause derived by resolving
    /// propagation reasons always passes
    fn refuted_by_propagation(af: &AF, query: usize, literals: &[Lit]) -> bool {
        let (mut node, result) = root(af, query);
        if result.is_err() {
            return true;
        }
        node.new_level();
        for &lit in literals {
            let result = match lit {
                Lit::In(a) => assume_out(a, &mut node, af),
                Lit::Out(a) => pseudo_complete(vec![a], &mut node, af),
                Lit::Def(_) => unreachable!("learned clauses have no Def literals"),
            };
            if result.is_err() {
                return true;
            }
        }
        false
    }

    // Explaining an only-defender assignment needs the other possible
    // defenders' being out, not just that the attacker must be defeated. 1
    // attacks the query 0, so must be defeated by 2, 3 or 5. Deciding 4
    // (level 1) puts its attacker 3 out; deciding 6 (level 2) puts 5 out,
    // forcing 2 in as the only defender left against 1. 8 attacks 6, so 6
    // needs 8's only attacker 7, but 2 attacks 7: conflict. Resolving it
    // back to the decision 6 runs through 2's reason, which is where 3 being
    // out enters: the clause is "6 out or 3 in", asserting 6 out at level 1.
    // Without 3 it would say 6 is never in, yet {0, 3, 6, 7, 9} is complete.
    #[test]
    fn test_only_defender_explanation() {
        let mut af = AF::new(10);
        for (a, b) in [(1, 0), (2, 1), (3, 1), (5, 1), (4, 3), (3, 4),
                       (6, 5), (2, 7), (7, 8), (8, 6), (2, 9), (9, 2)] {
            af.add_attack(a, b);
        }
        let (mut node, result) = root(&af, 0);
        assert!(result.is_ok());
        node.new_level();
        assert!(pseudo_complete(vec![4], &mut node, &af).is_ok());
        node.new_level();
        let conflict = pseudo_complete(vec![6], &mut node, &af)
            .expect_err("2 and 7 are both forced in");

        let learned = analyze(conflict, &node, &af).expect("explainable");
        assert_eq!(learned.literals, vec![Lit::Out(6), Lit::In(3)]);
        assert_eq!(learned.assertion_level, 1);
        let extension = HashSet::from([0, 3, 6, 7, 9]);
        assert!(af.is_complete(&extension));
        assert!(satisfies(&extension, &learned.literals));
    }

    /// How many assignments made since the trail was `before` long were
    /// forced by a learned clause
    fn clause_forced_since(node: &Node, before: usize) -> usize {
        node.trail()[before.min(node.trail().len())..].iter()
            .filter(|&&l| matches!(l, Lit::In(a) | Lit::Out(a) if matches!(node.reason(a), Reason::Clause(_))))
            .count()
    }

    /// Three mutual-attack pairs (0,1), (2,3), (4,5) and nothing forced at
    /// the root, with the clause "0, 2 or 4 is in" learned; deciding 1 and
    /// then 3 puts 0 and 2 out
    fn pairs_with_clause() -> (AF, Node) {
        let mut af = AF::new(6);
        for (a, b) in [(0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 4)] {
            af.add_attack(a, b);
        }
        let mut node = Node::new(&af, Semantics::Complete);
        node.clauses_mut().add_clause(vec![Lit::In(0), Lit::In(2), Lit::In(4)], 3);
        node.new_level();
        assert!(pseudo_complete(vec![1], &mut node, &af).is_ok());
        assert!(node.is_out(0) && node.value(2) == Value::Undecided);
        (af, node)
    }

    // Once two of the clause's literals are false, the watches force the
    // third, for the clause as reason.
    #[test]
    fn test_clause_becomes_unit() {
        let (af, mut node) = pairs_with_clause();
        node.new_level();
        assert!(pseudo_complete(vec![3], &mut node, &af).is_ok());
        assert!(node.contains(4), "the clause forces 4 once 0 and 2 are out");
        assert_eq!(node.reason(4), Reason::Clause(0));
        assert_eq!(node.level(4), 2);
        assert!(node.is_out(5), "and the closure propagates it on");
        node.check_clauses();
    }

    // A clause whose last two literals are falsified in one propagation
    // step, before the watches get to it, is a conflict of its own. 7
    // attacks both 2 and 4, and 0 is already out.
    #[test]
    fn test_clause_becomes_falsified() {
        let mut af = AF::new(9);
        for (a, b) in [(0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 4), (7, 8), (8, 7), (7, 2), (7, 4)] {
            af.add_attack(a, b);
        }
        let mut node = Node::new(&af, Semantics::Complete);
        node.clauses_mut().add_clause(vec![Lit::In(0), Lit::In(2), Lit::In(4)], 3);
        node.new_level();
        assert!(pseudo_complete(vec![1], &mut node, &af).is_ok());
        node.new_level();
        let conflict = pseudo_complete(vec![7], &mut node, &af).expect_err("all false");
        assert_eq!(conflict, Conflict::Clause(0));
        let learned = analyze(conflict, &node, &af).expect("explainable");
        // Resolving through the member 7: 7 is out, or 0 is in
        assert_eq!(learned.literals, vec![Lit::Out(7), Lit::In(0)]);
        assert_eq!(learned.assertion_level, 1);
    }

    // A conflict reached through a clause-forced argument is explained by
    // the clause's other literals. Deciding 3 puts 2 out, which makes the
    // clause force 4 in; 2 was also the only attacker of 6, so completeness
    // forces 6 in -- and 6 attacks 4.
    #[test]
    fn test_conflict_through_clause_forced_argument() {
        let mut af = AF::new(7);
        for (a, b) in [(0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 4), (2, 6), (6, 4)] {
            af.add_attack(a, b);
        }
        let mut node = Node::new(&af, Semantics::Complete);
        node.clauses_mut().add_clause(vec![Lit::In(0), Lit::In(2), Lit::In(4)], 3);
        node.new_level();
        assert!(pseudo_complete(vec![1], &mut node, &af).is_ok());
        node.new_level();
        let conflict = pseudo_complete(vec![3], &mut node, &af).expect_err("6 attacks 4");
        assert_eq!(conflict, Conflict::Clash { arg: 6, reason: Reason::Member(4) });
        let learned = analyze(conflict, &node, &af).expect("explainable");
        // 4 was forced because 0 and 2 are out, 6 because 2 is out, and 2
        // is out because of 3: so either 3 is out or 0 is in
        assert_eq!(learned.literals, vec![Lit::Out(3), Lit::In(0)]);
        assert_eq!(learned.assertion_level, 1);
    }

    /// Run the CDCL loop on `af` for `query`: random decisions, and on each
    /// conflict learn, backjump to the assertion level, assert the first
    /// literal and propagate, now and then restarting from level 0 instead.
    /// Checks the learned clauses at every step, and that a YES comes with
    /// a complete extension containing the query. Returns the answer and
    /// how many clauses were learned and assignments forced by watches.
    fn cdcl(af: &AF, query: usize, rng: &mut Rng) -> (bool, usize, usize) {
        let n = af.argument_count();
        let (mut node, mut result) = root(af, query);
        let mut analyzer = Analyzer::new(n);
        let mut activity = Activity::new((0..n).collect());
        let mut learned_count = 0;
        let mut watch_forced = 0;
        let mut steps = 0;
        let answer = loop {
            steps += 1;
            assert!(steps < 100_000, "the search does not terminate\n{af}");
            match result {
                Err(conflict) => {
                    let learned = analyzer.analyze(conflict, &node, af, &mut activity)
                        .expect("decisions are only made on undecided arguments");
                    learned_count += 1;
                    if learned.literals.is_empty() {
                        break false;
                    }
                    let first = learned.literals[0];
                    let level = learned.assertion_level;
                    let idx = node.clauses_mut().add_clause(learned.literals, learned.lbd);
                    if level > 0 && rng.below(8) == 0 {
                        // Restart: the clause stays, and may well become unit
                        // again under the next decisions -- which is what
                        // exercises the watches. A unit clause has no
                        // watches and is asserted below instead, as a fact
                        // at level 0.
                        backtrack_to_level(0, &mut node, af);
                        result = Ok(());
                        continue;
                    }
                    backtrack_to_level(level, &mut node, af);
                    let before = node.trail().len();
                    result = assign_literal(first, Reason::Clause(idx), &mut node)
                        .and_then(|()| propagate(&mut node, af));
                    // Everything the clauses forced beyond the assertion
                    watch_forced += clause_forced_since(&node, before).saturating_sub(1);
                }
                Ok(()) => {
                    node.check_clauses();
                    if node.is_self_defending(af) {
                        let extension = node.arguments();
                        assert!(extension.contains(&query) && af.is_complete(&extension),
                            "{extension:?} is not a complete extension with {query}\n{af}");
                        break true;
                    }
                    let undecided: Vec<usize> = (0..n)
                        .filter(|&a| node.value(a) == Value::Undecided)
                        .collect();
                    assert!(!undecided.is_empty(), "stuck\n{af}");
                    let c = undecided[rng.below(undecided.len())];
                    node.new_level();
                    let before = node.trail().len();
                    result = pseudo_complete(vec![c], &mut node, af);
                    watch_forced += clause_forced_since(&node, before);
                }
            }
        };
        (answer, learned_count, watch_forced)
    }

    /// A query of `af` whose root closure is consistent but not yet a
    /// complete extension, so that answering it takes a search, if any
    fn searching_query(af: &AF, rng: &mut Rng) -> Option<usize> {
        let n = af.argument_count();
        let start = rng.below(n);
        (0..n).map(|k| (start + k) % n).find(|&q| {
            let (node, result) = root(af, q);
            result.is_ok() && !node.is_self_defending(af)
        })
    }

    // The CDCL loop agrees with brute force on small random frameworks.
    #[test]
    fn test_cdcl_loop_matches_brute_force() {
        let mut rng = Rng::new(6);
        let mut rounds = 0;
        let mut learned = 0;
        let mut watch_forced = 0;
        for _ in 0..10_000 {
            let n = 2 + rng.below(11);
            let percent = [10, 20, 35, 50][rng.below(4)];
            let af = random_af(&mut rng, n, percent);
            let Some(query) = searching_query(&af, &mut rng) else { continue };
            let expected = !extensions_containing(&af, query).is_empty();
            let (answer, l, w) = cdcl(&af, query, &mut rng);
            assert_eq!(answer, expected, "query {query}\n{af}");
            rounds += 1;
            learned += l;
            watch_forced += w;
        }
        assert!(rounds > 500, "too few frameworks needed a search ({rounds})");
        assert!(learned > 500, "too few clauses learned ({learned})");
        // Watches hardly ever fire here: the searches are too short for a
        // clause to come up again. The medium frameworks cover that.
        let _ = watch_forced;
    }

    // The CDCL loop agrees with the chronological search on medium random
    // frameworks, where searches are long enough for learned clauses to
    // come up again and propagate through their watches.
    #[test]
    fn test_cdcl_loop_matches_dc_co() {
        let mut rng = Rng::new(7);
        let mut rounds = 0;
        let mut learned = 0;
        let mut watch_forced = 0;
        for _ in 0..2000 {
            let n = 15 + rng.below(26);
            let percent = [5, 8, 12][rng.below(3)];
            let af = random_af(&mut rng, n, percent);
            let Some(query) = searching_query(&af, &mut rng) else { continue };
            let expected = dc_co(&af, query, false).is_some();
            let (answer, l, w) = cdcl(&af, query, &mut rng);
            assert_eq!(answer, expected, "query {query}\n{af}");
            rounds += 1;
            learned += l;
            watch_forced += w;
        }
        assert!(rounds > 500, "too few frameworks needed a search ({rounds})");
        assert!(learned > 1000, "too few clauses learned ({learned})");
        assert!(watch_forced > 100, "too few assignments forced by watches ({watch_forced})");
    }
    // A query whose root closure is contradictory gives the empty clause,
    // and then no complete extension contains it.
    #[test]
    fn test_root_conflict_learns_empty_clause() {
        let mut rng = Rng::new(5);
        let mut refuted = 0;
        for _ in 0..1000 {
            let n = 2 + rng.below(9);
            let percent = [10, 20, 35, 50][rng.below(4)];
            let af = random_af(&mut rng, n, percent);
            let query = rng.below(n);
            let (node, result) = root(&af, query);
            let Err(conflict) = result else { continue };
            let learned = analyze(conflict, &node, &af).expect("level 0 always explains");
            assert!(learned.literals.is_empty());
            assert!(extensions_containing(&af, query).is_empty(), "refuted, but YES\n{af}");
            refuted += 1;
        }
        assert!(refuted > 300, "too few refuted queries ({refuted}) to mean much");
    }

    // On random frameworks, close a query that survives its root closure,
    // then make random decisions -- and sometimes assume arguments out --
    // until propagation runs into a conflict, and check the learned
    // clause: every complete extension containing the query satisfies it
    // (brute force), assuming it false makes propagation fail again,
    // the assignment it was learned from falsifies it, and,
    // when nothing was assumed out at the conflict level, it has exactly one
    // literal there and asserts below it.
    #[test]
    fn test_learned_clauses_random() {
        let mut rng = Rng::new(4);
        let mut learned_count = 0;
        let mut asserting_count = 0;
        for round in 0..10000 {
            let n = 2 + rng.below(11);
            let percent = [10, 20, 35, 50][rng.below(4)];
            let af = random_af(&mut rng, n, percent);
            let start = rng.below(n);
            let Some((query, mut node)) = (0..n)
                .map(|k| (start + k) % n)
                .map(|query| (query, root(&af, query)))
                .find_map(|(query, (node, result))| result.is_ok().then_some((query, node)))
            else {
                continue;
            };

            let mut result = Ok(());
            let mut ruled_out_at = HashSet::new();
            while result.is_ok() {
                let undecided: Vec<usize> = (0..n)
                    .filter(|&a| node.value(a) == Value::Undecided)
                    .collect();
                if undecided.is_empty() {
                    break;
                }
                let c = undecided[rng.below(undecided.len())];
                // Not at level 0, whose assignments analysis takes as facts
                if node.decision_level() > 0 && rng.below(4) == 0 {
                    ruled_out_at.insert(node.decision_level());
                    result = assume_out(c, &mut node, &af);
                } else {
                    node.new_level();
                    result = pseudo_complete(vec![c], &mut node, &af);
                }
            }
            let Err(conflict) = result else { continue };
            let learned = analyze(conflict, &node, &af)
                .expect("search assumptions are only made on undecided arguments");
            learned_count += 1;

            for extension in &extensions_containing(&af, query) {
                assert!(
                    satisfies(extension, &learned.literals),
                    "round {round}: {:?} excludes the complete extension {extension:?}\n{af}",
                    learned.literals
                );
            }
            assert!(
                refuted_by_propagation(&af, query, &learned.literals),
                "round {round}: {:?} does not follow by propagation\n{af}",
                learned.literals
            );
            for &lit in &learned.literals {
                let falsified = match lit {
                    Lit::In(a) => node.is_out(a),
                    Lit::Out(a) => node.contains(a),
                    Lit::Def(_) => false,
                };
                assert!(falsified, "round {round}: {lit:?} is not false under the assignment");
            }
            if learned.literals.is_empty() {
                continue;
            }
            // The second literal is the other watch, and must be the one
            // undone last on backtracking: the one at the assertion level
            if let Some(&second) = learned.literals.get(1) {
                assert_eq!(node.level(second.arg()), learned.assertion_level,
                    "round {round}: {:?} does not watch its assertion-level literal", learned.literals);
            }
            let level = node.level(learned.literals[0].arg());
            if !ruled_out_at.contains(&level) {
                let at_level = learned.literals.iter()
                    .filter(|&&l| node.level(l.arg()) == level)
                    .count();
                assert_eq!(at_level, 1, "round {round}: {:?} is not asserting", learned.literals);
                assert!(learned.assertion_level < level);
                asserting_count += 1;
            }
        }
        assert!(learned_count > 1000, "too few conflicts ({learned_count}) to mean much");
        assert!(asserting_count > 500, "too few asserting clauses ({asserting_count})");
    }
}
