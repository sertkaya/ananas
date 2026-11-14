use crate::af::AF;
use crate::algorithms::clauses::propagate_clauses;
use crate::algorithms::lit::{Assignment, Lit, Reason, Semantics, Value};
use crate::algorithms::node::Node;

/// A contradiction that propagation ran into
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Conflict {
    /// `arg` would have to get the opposite of the value it has, for
    /// `reason`
    Clash { arg: usize, reason: Reason },
    /// The argument must be defeated, but every one of its attackers is out
    NoDefender(usize),
    /// Every literal of the learned clause with the given index is false
    Clause(usize),
}

/// Make `lit` hold for `reason`. Fails if its opposite already holds.
pub fn assign_literal(lit: Lit, reason: Reason, node: &mut Node) -> Result<(), Conflict> {
    match lit {
        Lit::In(a) => set_in(a, reason, node),
        Lit::Out(a) => set_out(a, reason, node),
        Lit::Def(_) => unreachable!("only In and Out literals are assigned by reason"),
    }
}

/// Put `arg` in the set for `reason`. Fails if `arg` is already out.
fn set_in(arg: usize, reason: Reason, node: &mut Node) -> Result<(), Conflict> {
    match node.assign(arg, Value::In, reason) {
        Assignment::Conflict => Err(Conflict::Clash { arg, reason }),
        _ => Ok(()),
    }
}

/// Rule `arg` out of the set for `reason`. Fails if `arg` is already in.
fn set_out(arg: usize, reason: Reason, node: &mut Node) -> Result<(), Conflict> {
    match node.assign(arg, Value::Out, reason) {
        Assignment::Conflict => Err(Conflict::Clash { arg, reason }),
        _ => Ok(()),
    }
}

/// Check whether the set still has a way to defend itself against `b`,
/// after `b` has become known defeated or one of its attackers has become
/// unusable.
///
/// With no usable defender left the set can never be defended against `b`,
/// so the branch is dead. With exactly one, that defender is forced --
/// there is no alternative to branch on.
///
/// The usable-defender count is decremented as out arguments are
/// propagated, so it can lag behind the assignment and only ever
/// overestimates. The cheap count settles the common case; below 2 the
/// defenders are checked exactly against the assignment.
///
/// Fails if the branch is dead.
fn resolve_defenders(b: usize, node: &mut Node, af: &AF) -> Result<(), Conflict> {
    if !node.known_defeated(b) || node.usable_defenders_count(b) > 1 {
        // Either nothing demands that `b` be defeated, or there is still a
        // choice of defenders: a flag and an array read, and nothing is
        // forced or settled.
        return Ok(());
    }
    if node.is_defeated(af, b) {
        // A member already attacks `b`, so the demand is met.
        return Ok(());
    }
    // At most one attacker can be anything but out, since the count bounds
    // them from above.
    match af.attackers(b).copied().find(|&c| !node.is_out(c)) {
        None => Err(Conflict::NoDefender(b)),
        Some(survivor) => set_in(survivor, Reason::OnlyDefender(b), node),
    }
}

/// Apply what propagating `lit` does to the node's counters. Done for the
/// whole of a literal before any assignment it triggers, so that a
/// conflict never leaves a literal's counter updates half done, and
/// `unapply` can reverse them exactly.
fn apply(lit: Lit, node: &mut Node, af: &AF) {
    match lit {
        Lit::In(m) => {
            // A member attacks each victim, so it is actually defeated by
            // the set so far -- which is what tells the search whether an
            // argument that must be defeated still needs a defender.
            for &v in af.victims(m) {
                node.add_in_attacker(v);
            }
        }
        Lit::Out(c) => {
            // `c` can no longer defend anything it attacks.
            for &v in af.victims(c) {
                node.decrement_usable_defenders(v);
            }
        }
        Lit::Def(b) => {
            // One more attacker of each of `b`'s victims is defeated in
            // every completion.
            for &v in af.victims(b) {
                node.decrement_undefeated_attackers(v);
            }
        }
    }
}

/// Reverse what `apply` did to the node's counters for `lit`
fn unapply(lit: Lit, node: &mut Node, af: &AF) {
    match lit {
        Lit::In(m) => {
            for &v in af.victims(m) {
                node.remove_in_attacker(v);
            }
        }
        Lit::Out(c) => {
            for &v in af.victims(c) {
                node.increment_usable_defenders(v);
            }
        }
        Lit::Def(b) => {
            for &v in af.victims(b) {
                node.increment_undefeated_attackers(v);
            }
        }
    }
}

/// Propagate the consequences of the assignments queued on `node`'s trail
/// until nothing more follows, extending `node` to its smallest
/// pseudo-complete superset.
///
/// Both closure rules rest on the same observation: an argument `b` is
/// defeated in *every* complete extension containing `node`'s current
/// arguments as soon as either a member attacks `b` (semi-complete) or `b`
/// attacks a member, since a complete extension defends its members and so
/// must attack `b` back (quasi-complete). Either way `b` is out and `Def(b)`
/// holds. Under stable semantics every out argument is defeated, so there
/// `Def(b)` follows from `Out(b)` alone. Once all of some argument's attackers are known defeated, it is
/// defended in every completion and is put in, whether or not it is
/// defended *yet* -- and since both routes feed the same counter, an
/// argument whose attackers are covered by a mixture of them is put in too.
/// Each argument that must be defeated also needs a usable defender: with
/// one left it is put in (the P-pseudo-complete rule of Section 4.2), with
/// none the branch is dead.
///
/// Learned clauses are propagated alongside: an argument's being decided
/// falsifies one literal about it, and any clause watching that literal is
/// looked at.
///
/// Every assignment is made eagerly, the moment it follows, and is only
/// propagated later, in trail order; so an argument's value is exact even
/// while the counters derived from it are catching up.
///
/// Fails as soon as an argument would have to be both in and out, or would
/// have to be defeated with no way left to defeat it, or a learned clause
/// has every literal false. The node is then
/// contradictory, and must be backtracked to before whatever assignment
/// was being propagated.
pub fn propagate(node: &mut Node, af: &AF) -> Result<(), Conflict> {
    while let Some(lit) = node.next_to_propagate() {
        apply(lit, node, af);
        match lit {
            Lit::In(m) => {
                for &v in af.victims(m) {
                    // Semi-complete: `v` conflicts with the set and is
                    // defeated in every completion.
                    set_out(v, Reason::Member(m), node)?;
                    node.assign_def(v, Lit::In(m));
                }
                for &b in af.attackers(m) {
                    // Quasi-complete: `b` conflicts with the set, and any
                    // completion must defend `m` by attacking `b` back.
                    set_out(b, Reason::Member(m), node)?;
                    node.assign_def(b, Lit::In(m));
                }
                propagate_clauses(lit, node)?;
            }
            Lit::Out(c) => {
                if node.semantics() == Semantics::Stable {
                    // A stable extension attacks everything outside it, so
                    // `c` must be defeated in every completion too.
                    node.assign_def(c, Lit::Out(c));
                }
                for &v in af.victims(c) {
                    resolve_defenders(v, node, af)?;
                }
                propagate_clauses(lit, node)?;
            }
            Lit::Def(b) => {
                // A victim of `b` with no attacker left that is not known
                // defeated is defended in every completion, so must be in.
                for &v in af.victims(b) {
                    if node.undefeated_attackers_count(v) == 0 {
                        set_in(v, Reason::Completeness, node)?;
                    }
                }
                // `b` must be defeated, so the set needs a defender against it.
                resolve_defenders(b, node, af)?;
            }
        }
    }
    Ok(())
}

/// Undo every assignment made after the trail was `len` long, reversing
/// their effect on the counters, so that `node` is exactly as it was then.
fn backtrack(len: usize, node: &mut Node, af: &AF) {
    while let Some((lit, was_propagated)) = node.unassign_last(len) {
        if was_propagated {
            unapply(lit, node, af);
        }
    }
}

/// Undo every decision level above `level`, so that `node` is exactly as
/// it was when the next level began.
pub fn backtrack_to_level(level: usize, node: &mut Node, af: &AF) {
    let len = node.drop_levels_above(level);
    backtrack(len, node, af);
}

/// Put the `seeds` in `node`'s set as assumptions and extend it with its
/// smallest pseudo-complete superset; see `propagate`.
///
/// Fails if that runs into a conflict, leaving `node` contradictory until
/// it is backtracked to before the seeds.
pub fn pseudo_complete(seeds: Vec<usize>, node: &mut Node, af: &AF) -> Result<(), Conflict> {
    for arg in seeds {
        set_in(arg, Reason::Decision, node)?;
    }
    propagate(node, af)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use crate::io::af_parser::read_af;
    use crate::algorithms::random_af::{random_af, Rng};

    /// Assume `arg` out, as the search's clauses may make it, and propagate
    fn assume_out(arg: usize, node: &mut Node, af: &AF) -> Result<(), Conflict> {
        assign_literal(Lit::Out(arg), Reason::Decision, node)?;
        propagate(node, af)
    }

    /// Check that every assignment in a node `propagate` has finished with
    /// is justified by its recorded reason, and that the node is a fixpoint
    /// of the closure rules.
    fn check_node(node: &Node, af: &AF) {
        for a in 0..af.argument_count() {
            match (node.value(a), node.reason(a)) {
                (Value::Undecided, _) => {}
                (Value::In, Reason::Decision) => {}
                (Value::In, Reason::Completeness) => assert!(
                    af.attackers(a).all(|&b| node.known_defeated(b)),
                    "{a} is in by completeness with an attacker not known defeated"
                ),
                (Value::In, Reason::OnlyDefender(b)) => {
                    assert!(af.attacks(a, b) && node.known_defeated(b));
                    assert!(
                        af.attackers(b).all(|&c| c == a || node.is_out(c)),
                        "{a} is not the only defender left against {b}"
                    );
                }
                (Value::Out, Reason::SelfAttack) => assert!(af.attacks(a, a)),
                (Value::Out, Reason::Decision) => {}
                (Value::Out, Reason::Member(m)) => assert!(
                    node.contains(m) && (af.attacks(m, a) || af.attacks(a, m)),
                    "{a} is out for conflicting with {m}, but does not"
                ),
                (value, reason) => panic!("{a} is {value:?} for {reason:?}"),
            }
            if node.known_defeated(a) {
                match node.def_source(a) {
                    Lit::In(m) => assert!(
                        node.contains(m) && (af.attacks(m, a) || af.attacks(a, m)),
                        "{a} is known defeated because of {m}, but neither attacks the other"
                    ),
                    Lit::Out(x) => assert!(x == a && node.semantics() == Semantics::Stable),
                    Lit::Def(_) => unreachable!(),
                }
                assert!(node.is_out(a), "{a} is known defeated but not out");
            }

            // Fixpoint: conflict-free, closed under the completeness rule,
            // and every argument that must be defeated either is or still
            // has a choice of defenders.
            if node.contains(a) {
                assert!(!node.is_defeated(af, a), "{a} is in and attacked by the set");
            }
            if af.attackers(a).all(|&b| node.known_defeated(b)) {
                assert!(node.contains(a), "{a} is defended in every completion but not in");
            }
            if node.known_defeated(a) && !node.is_defeated(af, a) {
                let usable = af.attackers(a).filter(|&&c| !node.is_out(c)).count();
                assert!(usable >= 2, "{a} has {usable} usable defenders but was not resolved");
            }
        }
    }

    // Backtracking restores the node exactly -- values, counters, trail --
    // after any mix of in and out assumptions on random frameworks,
    // including ones that ended in a conflict partway through propagating.
    #[test]
    fn test_backtrack_restores_state_random() {
        let mut rng = Rng::new(3);
        let mut conflicts = 0;
        for _ in 0..2000 {
            let n = 2 + rng.below(11);
            let percent = [10, 20, 35, 50][rng.below(4)];
            let af = random_af(&mut rng, n, percent);
            let mut node = Node::new(&af, Semantics::Complete);
            let mut seeds = vec![rng.below(n)];
            seeds.extend((0..n).filter(|&a| af.attacker_count(a) == 0));
            if pseudo_complete(seeds, &mut node, &af).is_err() {
                conflicts += 1;
                backtrack(0, &mut node, &af);
                node.assert_same_state(&Node::new(&af, Semantics::Complete));
                continue;
            }
            let snapshot = node.clone();
            for _ in 0..1 + rng.below(3) {
                node.new_level();
                let undecided: Vec<usize> = (0..n)
                    .filter(|&a| node.value(a) == Value::Undecided)
                    .collect();
                if undecided.is_empty() {
                    break;
                }
                let c = undecided[rng.below(undecided.len())];
                let consistent = if rng.below(2) == 0 {
                    pseudo_complete(vec![c], &mut node, &af).is_ok()
                } else {
                    assume_out(c, &mut node, &af).is_ok()
                };
                if !consistent {
                    conflicts += 1;
                    break;
                }
            }
            backtrack_to_level(0, &mut node, &af);
            node.assert_same_state(&snapshot);
        }
        assert!(conflicts > 200, "too few conflicts ({conflicts}) to test undoing them");
    }

    // Every assignment the closure makes, on random frameworks seeded the
    // way dc_co seeds them and then with a further argument assumed out, is
    // justified by its reason, and the result is a fixpoint.
    #[test]
    fn test_propagate_reasons_random() {
        let mut rng = Rng::new(1);
        let mut checked = 0;
        for _ in 0..2000 {
            let n = 2 + rng.below(11);
            let percent = [10, 20, 35, 50][rng.below(4)];
            let af = random_af(&mut rng, n, percent);
            let mut node = Node::new(&af, Semantics::Complete);
            let mut seeds = vec![rng.below(n)];
            seeds.extend((0..n).filter(|&a| af.attacker_count(a) == 0));
            if pseudo_complete(seeds, &mut node, &af).is_err() {
                continue;
            }
            check_node(&node, &af);
            checked += 1;
            let undecided: Vec<usize> = (0..n)
                .filter(|&a| node.value(a) == Value::Undecided)
                .collect();
            if !undecided.is_empty() {
                let c = undecided[rng.below(undecided.len())];
                if assume_out(c, &mut node, &af).is_ok() {
                    check_node(&node, &af);
                }
            }
        }
        assert!(checked > 500, "too few consistent closures ({checked}) to mean much");
    }

    // Chain 0 -> 1 -> 2 -> 3: only 0 and 2 belong to the grounded/complete closure
    fn build_af() -> AF {
        let mut af = AF::new(4);
        af.add_attack(0, 1);
        af.add_attack(1, 2);
        af.add_attack(2, 3);
        af
    }

    #[test]
    fn test_pseudo_complete() {
        let af = build_af();
        let mut node = Node::new(&af, Semantics::Complete);

        assert!(pseudo_complete(vec![0], &mut node, &af).is_ok());

        assert!(node.contains(0));
        assert!(!node.contains(1));
        assert!(node.contains(2));
        assert!(!node.contains(3));

        println!("{}", node);
    }

    // Every argument in jelia23-example.af has at least one attacker, so no
    // argument is unconditionally defended and the closure stays empty.
    #[test]
    fn test_pseudo_complete_jelia23() -> std::io::Result<()> {
        let input_af = File::open("tests/jelia23-example.af")?;
        let af = read_af(input_af);
        let mut node = Node::new(&af, Semantics::Complete);

        // Seed the closure the way a real caller would: with the
        // arguments that are unconditionally defended from the start.
        let mut update = Vec::new();
        for arg in 0..af.argument_count() {
            if af.attacker_count(arg) == 0 {
                update.push(arg);
            }
        }

        assert!(pseudo_complete(update, &mut node, &af).is_ok());

        for arg in 0..af.argument_count() {
            assert!(!node.contains(arg));
        }

        println!("{}", node);
        Ok(())
    }

    // Regression test: jelia23-example.af has a mutual attack 0<->1. If an
    // already-accepted argument (0) got re-pushed and re-processed via the
    // cycle, its own unattacked-attacker count would be decremented past
    // what it started at, underflowing. The propagation flags must stop that.
    #[test]
    fn test_pseudo_complete_mutual_attack_cycle() -> std::io::Result<()> {
        let input_af = File::open("tests/jelia23-example.af")?;
        let af = read_af(input_af);
        let mut node = Node::new(&af, Semantics::Complete);

        assert!(pseudo_complete(vec![0], &mut node, &af).is_ok());

        assert!(node.contains(0));
        assert!(!node.contains(1));
        assert!(!node.contains(2));
        assert!(!node.contains(3));
        assert!(!node.contains(4));

        println!("{}", node);
        Ok(())
    }

    // Odd attack cycle 0 -> 1 -> 2 -> 0: no argument in it can ever be part
    // of a conflict-free set, since forcing any one in eventually propagates
    // an attack back onto itself.
    #[test]
    fn test_pseudo_complete_conflict() {
        let mut af = AF::new(3);
        af.add_attack(0, 1);
        af.add_attack(1, 2);
        af.add_attack(2, 0);
        let mut node = Node::new(&af, Semantics::Complete);

        assert!(pseudo_complete(vec![0], &mut node, &af).is_err());
    }

    // Regression test: 0 and 1 both attack 2 (attacker_count(2)=2); 2 and 4
    // both attack 3 (attacker_count(3)=2); 4 self-attacks so it can never be
    // defeated. 3 must stay excluded, since its attacker 4 is never defeated
    // -- only 2 is. Without deduplicating "victim is defeated" per victim,
    // 2's single defeat would get double-counted (once via 0, once via 1)
    // and incorrectly satisfy both of 3's needed decrements.
    #[test]
    fn test_pseudo_complete_shared_intermediate() {
        let mut af = AF::new(5);
        af.add_attack(0, 2);
        af.add_attack(1, 2);
        af.add_attack(2, 3);
        af.add_attack(4, 3);
        af.add_attack(4, 4);
        let mut node = Node::new(&af, Semantics::Complete);

        assert!(pseudo_complete(vec![0, 1], &mut node, &af).is_ok());

        println!("{}", node);
        assert!(!node.contains(3), "3's attacker 4 was never defeated");
    }

    // 0 -> 1 -> 2: forcing 0 in organically pulls in 2 (via 1's defeat), with
    // no direct conflict. If 2 is already out (e.g. by a learned clause),
    // the closure must still reject it, even though 2 does not conflict with
    // anything in the set.
    #[test]
    fn test_pseudo_complete_already_out() {
        let mut af = AF::new(3);
        af.add_attack(0, 1);
        af.add_attack(1, 2);
        let mut node = Node::new(&af, Semantics::Complete);
        assert!(assume_out(2, &mut node, &af).is_ok());

        assert!(pseudo_complete(vec![0], &mut node, &af).is_err());
    }

    // Quasi-complete rule in isolation: 0 -> 1 -> 2 means forcing 0 in
    // defeats 1, defending 2 (semi-complete). Separately, 3 -> 0 makes 3 an
    // attacker of the set from the start, and 3 -> 4 means 4's only
    // attacker (3) also attacks the set -- so 4 must be added too, even
    // though 3 itself is never defeated and 4 is therefore not defended.
    //
    // 5 and 6 attack 3 and each other. They keep 3 from being unattacked --
    // an unattacked attacker of the set could never be defeated, so the
    // branch would be dead and there would be no pseudo-complete superset
    // at all -- while leaving 3 two possible defenders, so neither the
    // single-defender rule nor the no-defender check resolves it first.
    #[test]
    fn test_pseudo_complete_quasi_complete() {
        let mut af = AF::new(7);
        af.add_attack(0, 1);
        af.add_attack(1, 2);
        af.add_attack(3, 0);
        af.add_attack(3, 4);
        af.add_attack(5, 3);
        af.add_attack(6, 3);
        af.add_attack(5, 6);
        af.add_attack(6, 5);
        let mut node = Node::new(&af, Semantics::Complete);

        assert!(pseudo_complete(vec![0], &mut node, &af).is_ok());

        println!("{}", node);
        assert!(node.contains(2), "2 is defended once 0 defeats its attacker 1");
        assert!(
            node.contains(4),
            "4's only attacker (3) also attacks the set, so quasi-complete must add it"
        );
    }

    // No-defender check: 1 attacks the target 0, and 1's only attacker 2 is
    // itself attacked by 0, so 2 conflicts with the set and can never be
    // added. Nothing else can defeat 1, so the set can never be defended
    // against it and the branch is dead -- pseudo_complete must say so
    // rather than leave the search to discover an empty candidate list.
    #[test]
    fn test_pseudo_complete_no_possible_defender() {
        let mut af = AF::new(3);
        af.add_attack(1, 0);
        af.add_attack(2, 1);
        af.add_attack(0, 2);
        let mut node = Node::new(&af, Semantics::Complete);

        assert!(pseudo_complete(vec![0], &mut node, &af).is_err());
    }

    // Mixed defeat routes: 3's two attackers are each known defeated by a
    // different route -- 1 because the member 0 attacks it (semi-complete),
    // 2 because it attacks the member 0, so any complete extension
    // containing 0 must attack it back (quasi-complete). Neither rule alone
    // covers all of 3's attackers, so tracking the routes in separate
    // counters leaves 3 unforced; sharing one counter forces it. 4 and 5
    // mutually attack and both attack 2, so 2 has two possible defenders
    // and the single-defender rule cannot resolve it instead.
    #[test]
    fn test_pseudo_complete_mixed_defeat_routes() {
        let mut af = AF::new(6);
        af.add_attack(0, 1);
        af.add_attack(1, 3);
        af.add_attack(2, 3);
        af.add_attack(2, 0);
        af.add_attack(4, 2);
        af.add_attack(5, 2);
        af.add_attack(4, 5);
        af.add_attack(5, 4);
        let mut node = Node::new(&af, Semantics::Complete);

        assert!(pseudo_complete(vec![0], &mut node, &af).is_ok());

        println!("{}", node);
        assert!(node.contains(3), "3's attackers are defeated by one route each");
        // The only complete extensions containing 0 are {0,3,4} and {0,3,5},
        // so 3 is forced but the choice between 4 and 5 is left to the search.
        assert!(!node.contains(4));
        assert!(!node.contains(5));
    }

    // Single-defender chain (paper Section 4.2 / Figure 3): forcing 0 in
    // leaves its attacker 1 undefeated; 1's only possible defender is 2, so
    // 2 must be forced in too, with no branching. That in turn leaves 2's
    // attacker 3 undefeated; 3's only possible defender is 4, so 4 gets
    // forced in as well -- a two-link forced chain resolved within this one
    // pseudo_complete call, yielding a complete extension directly.
    #[test]
    fn test_pseudo_complete_single_defender_chain() {
        let mut af = AF::new(5);
        af.add_attack(1, 0);
        af.add_attack(2, 1);
        af.add_attack(3, 2);
        af.add_attack(4, 3);
        let mut node = Node::new(&af, Semantics::Complete);

        assert!(pseudo_complete(vec![0], &mut node, &af).is_ok());

        println!("{}", node);
        assert!(node.contains(2), "2 is 1's only possible defender");
        assert!(node.contains(4), "4 is 3's only possible defender");
        assert!(node.is_self_defending(&af));
    }
}
