use std::collections::HashSet;
use crate::af::AF;
use crate::algorithms::closure::pseudo_complete;
use crate::algorithms::node::Node;

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

    let mut stack: Vec<Node> = vec![current_node];

    while let Some(current_node) = stack.pop() {
        // current_node is guaranteed not self-defending: nothing else ever
        // gets pushed onto the stack. Find, among the undefeated attackers
        // of its undefended members, the one with the fewest non-prohibited
        // attackers of its own -- the most constrained argument to defeat.
        let mut best_attacker: Option<usize> = None;
        let mut best_count = usize::MAX;
        for m in 0..af.argument_count() {
            if !current_node.contains(m) || current_node.unattacked_attackers_count(m) == 0 {
                continue;
            }
            for &b in af.attackers(m) {
                if current_node.is_defeated(af, b) {
                    continue;
                }
                let count = af.attackers(b).filter(|&&c| !current_node.is_prohibited(c)).count();
                if count < best_count {
                    best_count = count;
                    best_attacker = Some(b);
                }
            }
        }

        let b = best_attacker
            .expect("a non-self-defending node must have an undefeated attacker");

        // Try each non-prohibited attacker of b as the argument to defeat it
        // with; close and check each candidate independently.
        for &c in af.attackers(b) {
            if current_node.is_prohibited(c) {
                continue;
            }
            let mut child = current_node.clone();
            if pseudo_complete(vec![c], &mut child, af) {
                if child.is_self_defending() {
                    return Some(child.arguments());
                }
                stack.push(child);
            }
        }
    }

    None
}
