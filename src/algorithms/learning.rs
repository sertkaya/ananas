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

use std::collections::HashSet;
use crate::af::AF;
use crate::algorithms::closure::Conflict;
use crate::algorithms::node::{Lit, Node, Reason, Value};

/// A clause learned from a conflict: a disjunction of in/out literals that
/// every complete extension containing the query satisfies, and that is
/// false under the assignment the conflict arose in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Learned {
    /// The literals. The first is the negated first unique implication
    /// point, the only literal at the conflict's decision level -- unless
    /// arguments were ruled out at that level, which keep their literals
    /// there too, since being ruled out has no antecedents to resolve.
    pub literals: Vec<Lit>,
    /// The highest decision level among the literals after the first:
    /// backjumping there leaves the first as the only one not yet false.
    /// 0 for a unit clause.
    pub assertion_level: usize,
}

/// The argument a literal is about
fn arg_of(lit: Lit) -> usize {
    match lit {
        Lit::In(a) | Lit::Out(a) | Lit::Def(a) => a,
    }
}

/// The literal that held when `b` became known defeated, standing in for
/// `Def(b)` itself
fn def_antecedent(b: usize, node: &Node) -> Lit {
    Lit::In(node.def_source(b))
}

/// Push to `out` the literals that implied giving `arg` a value for
/// `reason`, all true when it was given. Returns `false`, pushing nothing,
/// for an assumption -- a decision or a ruling-out -- which has none.
fn antecedents(arg: usize, reason: Reason, node: &Node, af: &AF, out: &mut Vec<Lit>) -> bool {
    match reason {
        Reason::Decision | Reason::RuledOut => return false,
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
    }
    Some(lits)
}

/// Derive a learned clause from `conflict`, which propagation has just run
/// into on `node` and which has not been backtracked yet.
///
/// Resolves the conflict back along the trail, through the antecedents of
/// each literal at the conflict's decision level, until a single literal at
/// that level is left -- the first unique implication point. Literals from
/// level 0 are dropped: they hold in every complete extension containing
/// the query. A conflict at level 0 gives the empty clause: no complete
/// extension contains the query.
///
/// Returns `None` if the conflict was an assumption above level 0
/// contradicting the assignment outright, which no clause can explain. At
/// level 0 the assumptions are the query and what follows from the
/// framework alone, so a contradiction among them gives the empty clause.
pub fn analyze(conflict: Conflict, node: &Node, af: &AF) -> Option<Learned> {
    let Some(conflict_lits) = conflict_literals(conflict, node, af) else {
        return (node.decision_level() == 0)
            .then(|| Learned { literals: Vec::new(), assertion_level: 0 });
    };
    let level = conflict_lits.iter().map(|&l| node.level(arg_of(l))).max().unwrap_or(0);
    if level == 0 {
        return Some(Learned { literals: Vec::new(), assertion_level: 0 });
    }

    // Literals from below the conflict level go straight into the clause,
    // negated; the ones at it are counted, and resolved away in reverse
    // trail order until one is left.
    let mut seen: HashSet<usize> = HashSet::new();
    let mut literals: Vec<Lit> = Vec::new();
    let mut pending = 0;
    let add = |lit: Lit, seen: &mut HashSet<usize>, literals: &mut Vec<Lit>| {
        let a = arg_of(lit);
        let lit_level = node.level(a);
        if lit_level == 0 || !seen.insert(a) {
            return 0;
        }
        if lit_level == level {
            1
        } else {
            literals.push(lit.negated());
            0
        }
    };
    for lit in conflict_lits {
        pending += add(lit, &mut seen, &mut literals);
    }

    let trail = node.trail();
    let mut i = trail.len();
    let mut buffer = Vec::new();
    let uip = loop {
        i -= 1;
        let lit = trail[i];
        let a = match lit {
            Lit::In(a) | Lit::Out(a) => a,
            Lit::Def(_) => continue,
        };
        if node.level(a) != level || !seen.contains(&a) {
            continue;
        }
        pending -= 1;
        if pending == 0 {
            break lit;
        }
        buffer.clear();
        if antecedents(a, node.reason(a), node, af, &mut buffer) {
            for &antecedent in &buffer {
                pending += add(antecedent, &mut seen, &mut literals);
            }
        } else {
            // A ruling-out at the conflict level: nothing to resolve it
            // with, so it stays.
            literals.push(lit.negated());
        }
    };

    literals.insert(0, uip.negated());
    let assertion_level = literals[1..].iter()
        .map(|&l| node.level(arg_of(l)))
        .max()
        .unwrap_or(0);
    Some(Learned { literals, assertion_level })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::closure::{pseudo_complete, rule_out};
    use crate::algorithms::random_af::{random_af, Rng};

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
        let mut node = Node::new(af);
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
                Lit::In(a) => rule_out(a, &mut node, af),
                Lit::Out(a) => pseudo_complete(vec![a], &mut node, af),
                Lit::Def(_) => unreachable!("learned clauses have no Def literals"),
            };
            if result.is_err() {
                return true;
            }
        }
        false
    }

    // Explaining an only-defender assignment needs the other defenders'
    // being out, not just that the attacker must be defeated. 1 attacks the
    // query 0, so must be defeated by 2, 3 or 5. Deciding 4 (level 1) puts
    // its attacker 3 out; deciding 6 (level 2) puts 5 out, forcing 2 in as
    // 1's only defender left. 8 attacks 6, so 6 needs 8's only attacker 7,
    // but 2 attacks 7: conflict. Resolving it back to the decision 6 runs
    // through 2's reason, which is where 3 being out enters: the clause is
    // "6 out or 3 in", asserting 6 out at level 1. Without 3 it would say
    // 6 is never in, yet {0, 3, 6, 7, 9} is complete.
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
    // then make random decisions -- and sometimes rule arguments out --
    // until propagation runs into a conflict, and check the learned
    // clause: every complete extension containing the query satisfies it
    // (brute force), assuming it false makes propagation fail again,
    // the assignment it was learned from falsifies it, and,
    // when nothing was ruled out at the conflict level, it has exactly one
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
                // Not at level 0, whose assignments analysis takes as facts:
                // a random ruling-out is no fact, unlike the search's, which
                // only rules out what a whole failed subtree has refuted.
                if node.decision_level() > 0 && rng.below(4) == 0 {
                    ruled_out_at.insert(node.decision_level());
                    result = rule_out(c, &mut node, &af);
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
            let level = node.level(arg_of(learned.literals[0]));
            if !ruled_out_at.contains(&level) {
                let at_level = learned.literals.iter()
                    .filter(|&&l| node.level(arg_of(l)) == level)
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
