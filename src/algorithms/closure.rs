use crate::af::AF;
use crate::algorithms::node::Node;

/// Extend `node` with the deterministic closure of the "defense" property of
/// complete extensions: an argument all of whose attackers have already been
/// defeated by `node`'s current arguments is itself added to `node`.
/// `update` is a stack of arguments to add to `node` and whose effect on the
/// unattacked-attacker counts of their attacked arguments' victims still
/// needs to be propagated.
///
/// Returns `false` as soon as an argument that would be added conflicts with
/// `node`'s current set (in either attack direction, including self-attack),
/// leaving `node` in a discarded, no-longer-meaningful state. Returns `true`
/// if the closure completed without any conflict.
#[must_use]
pub fn pseudo_complete(mut update: Vec<usize>, node: &mut Node, af: &AF) -> bool {
    // Mark the seed arguments as added up front, before any propagation, so
    // that a seed sitting deeper on the stack is already prohibited if some
    // other seed's propagation happens to target it first.
    for &arg in &update {
        if node.conflicts_with(af, arg) {
            return false;
        }
        node.add_argument(arg);
    }

    while let Some(arg) = update.pop() {
        for &victim in af.victims(arg) {
            // `victim` being defeated is a one-time fact: if another of its
            // attackers already got accepted earlier and propagated this,
            // doing it again would double-count `victim`'s defeat against
            // its own victims' counts.
            if node.defeat_propagated(victim) {
                continue;
            }
            node.mark_defeat_propagated(victim);

            for &victim_of_victim in af.victims(victim) {
                // No is_prohibited guard here: defeat_propagated already
                // ensures each real attacker of victim_of_victim contributes
                // at most one decrement (deduplicated per attacker, not per
                // target), so this can never be called more times than
                // victim_of_victim's original attacker count -- including
                // for forced/seeded arguments, whose count must keep being
                // updated after they're already in the set.
                if node.decrement_unattacked_attackers(victim_of_victim) == 0 {
                    if node.conflicts_with(af, victim_of_victim) {
                        return false;
                    }
                    node.add_argument(victim_of_victim);
                    update.push(victim_of_victim);
                }
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use crate::io::af_parser::read_af;

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
        let mut node = Node::new(&af);

        assert!(pseudo_complete(vec![0], &mut node, &af));

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
        let mut node = Node::new(&af);

        // Seed the update stack the way a real caller would: with the
        // arguments that are unconditionally defended from the start.
        let mut update = Vec::new();
        for arg in 0..af.argument_count() {
            if af.attacker_count(arg) == 0 {
                update.push(arg);
            }
        }

        assert!(pseudo_complete(update, &mut node, &af));

        for arg in 0..af.argument_count() {
            assert!(!node.contains(arg));
        }

        println!("{}", node);
        Ok(())
    }

    // Regression test: jelia23-example.af has a mutual attack 0<->1. If an
    // already-accepted argument (0) got re-pushed and re-processed via the
    // cycle, its own unattacked-attacker count would be decremented past
    // what it started at, underflowing. `is_prohibited` must stop that.
    #[test]
    fn test_pseudo_complete_mutual_attack_cycle() -> std::io::Result<()> {
        let input_af = File::open("tests/jelia23-example.af")?;
        let af = read_af(input_af);
        let mut node = Node::new(&af);

        assert!(pseudo_complete(vec![0], &mut node, &af));

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
        let mut node = Node::new(&af);

        assert!(!pseudo_complete(vec![0], &mut node, &af));
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
        let mut node = Node::new(&af);

        assert!(pseudo_complete(vec![0, 1], &mut node, &af));

        println!("{}", node);
        assert!(!node.contains(3), "3's attacker 4 was never defeated");
    }
}
