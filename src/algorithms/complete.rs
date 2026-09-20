use std::collections::HashSet;
use crate::af::AF;
use crate::algorithms::closure::pseudo_complete;
use crate::algorithms::node::Node;

/// A node of the search tree paired with the candidate arguments still to
/// be tried, lazily, for defeating its most constrained undefeated attacker.
struct Frame {
    node: Node,
    candidates: Vec<usize>,
}

/// Among `node`'s undefended members' undefeated attackers, find the one
/// with the fewest non-prohibited attackers of its own -- the most
/// constrained argument to defeat -- and return its non-prohibited
/// attackers as the candidates to try defeating it with.
///
/// `node` must not be self-defending, i.e. some member must have an
/// undefeated attacker.
fn candidates(node: &Node, af: &AF) -> Vec<usize> {
    let mut best_attacker: Option<usize> = None;
    let mut best_count = usize::MAX;
    for m in 0..af.argument_count() {
        if !node.contains(m) || node.unattacked_attackers_count(m) == 0 {
            continue;
        }
        for &b in af.attackers(m) {
            if node.is_defeated(af, b) {
                continue;
            }
            let count = af.attackers(b).filter(|&&c| !node.is_prohibited(c)).count();
            if count < best_count {
                best_count = count;
                best_attacker = Some(b);
            }
        }
    }

    let b = best_attacker
        .expect("a non-self-defending node must have an undefeated attacker");

    af.attackers(b).filter(|&c| !node.is_prohibited(*c)).copied().collect()
}

/// Decide DC-CO: is `arg` credulously accepted with respect to the complete
/// semantics? Returns the complete extension of `af` containing `arg` if one
/// exists, `None` otherwise.
pub fn dc_co(af: &AF, arg: usize) -> Option<HashSet<usize>> {
    let mut current_node = Node::new(af);

    // We hypothesize that `arg` is in the extension, and arguments with no
    // attackers are defended by default, so both go onto the update stack;
    // pseudo_complete adds them to `current_node` before propagating their effects.
    let mut update = vec![arg];
    for a in 0..af.argument_count() {
        if af.attacker_count(a) == 0 {
            update.push(a);
        }
    }

    if !pseudo_complete(update, &mut current_node, af) {
        // The hypothesis that `arg` is in the extension is already
        // contradictory: closing it produced a conflict.
        return None;
    }

    if current_node.is_self_defending() {
        // node_args is conflict-free (checked above) and closed under
        // defense (guaranteed by pseudo_complete), and now every argument
        // in it defends itself: that's exactly a complete extension.
        return Some(current_node.arguments());
    }

    let root_candidates = candidates(&current_node, af);
    let mut stack: Vec<Frame> = vec![Frame { node: current_node, candidates: root_candidates }];

    while let Some(mut frame) = stack.pop() {
        // Take just one untried candidate; leave the rest for later, so a
        // sibling is only ever generated once this candidate's whole
        // subtree has been fully explored and abandoned.
        let Some(c) = frame.candidates.pop() else {
            continue;
        };

        let mut child = frame.node.clone();
        if !frame.candidates.is_empty() {
            stack.push(frame);
        }

        if pseudo_complete(vec![c], &mut child, af) {
            if child.is_self_defending() {
                return Some(child.arguments());
            }
            let child_candidates = candidates(&child, af);
            stack.push(Frame { node: child, candidates: child_candidates });
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dc_co_trivial() {
        // 0 has no attackers, so it's unconditionally in -- resolved at the
        // root, no search needed.
        let af = AF::new(1);
        let extension = dc_co(&af, 0).expect("0 has no attackers, must be accepted");
        assert!(extension.contains(&0));
    }

    #[test]
    fn test_dc_co_none() {
        // Odd cycle 0 -> 1 -> 2 -> 0: no complete extension can contain 0.
        let mut af = AF::new(3);
        af.add_attack(0, 1);
        af.add_attack(1, 2);
        af.add_attack(2, 0);
        assert!(dc_co(&af, 0).is_none());
    }

    #[test]
    fn test_dc_co_branching() {
        // 1 attacks 0 (our target); 2 and 3 both attack 1 and mutually
        // attack each other, so neither is unconditionally in -- the search
        // must pick one of them as a hypothesis to defeat 1.
        let mut af = AF::new(4);
        af.add_attack(1, 0);
        af.add_attack(2, 1);
        af.add_attack(3, 1);
        af.add_attack(2, 3);
        af.add_attack(3, 2);

        let extension = dc_co(&af, 0).expect("1 can be defeated by either 2 or 3");
        assert!(extension.contains(&0));
        assert!(extension.contains(&2) || extension.contains(&3));
        assert!(!(extension.contains(&2) && extension.contains(&3)));
    }
}
