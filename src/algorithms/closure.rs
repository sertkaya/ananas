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
            for &victim_of_victim in af.victims(victim) {
                if node.is_prohibited(victim_of_victim) {
                    continue;
                }
                if node.decrement_unattacked_attackers(victim_of_victim) == 0 {
                    if node.conflicts_with(af, victim_of_victim) {
                        return false;
                    }
                    // Must stay here, right when the count hits 0: if this is
                    // deferred until victim_of_victim is popped, a second
                    // attacker of it defeated in this same sweep would
                    // decrement it again below 0 before it's ever marked
                    // prohibited.
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
}
