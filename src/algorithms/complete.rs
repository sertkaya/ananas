use std::collections::HashSet;
use crate::af::AF;
use crate::algorithms::closure::pseudo_complete;
use crate::algorithms::node::Node;

/// A node of the search tree paired with the candidate arguments still to
/// be tried, lazily, for defeating its most constrained undefeated attacker,
/// and the arguments already known (from earlier failed candidates tried at
/// or above this point) to be unsuitable for this branch.
struct Frame {
    node: Node,
    candidates: Vec<usize>,
    prohibited_candidates: HashSet<usize>,
    // The candidate whose subtree we just pushed on top of this frame, if
    // any. If this frame is popped again while this is set, that subtree
    // must have failed entirely without success (a success would have
    // returned from the whole search already), so the candidate belongs in
    // prohibited_candidates before we try anything else from this frame.
    pending_candidate: Option<usize>,
}

/// Among `node`'s undefended members' undefeated attackers, find the one
/// with the fewest attackers of its own that are neither already decided
/// nor in `prohibited_candidates` -- the most constrained argument to
/// defeat -- and return those attackers as the candidates to try defeating
/// it with.
///
/// `node` must not be self-defending, i.e. some member must have an
/// undefeated attacker.
fn candidates(node: &Node, af: &AF, prohibited_candidates: &HashSet<usize>) -> Vec<usize> {
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
            let count = af.attackers(b)
                .filter(|&&c| !node.is_prohibited(c) && !prohibited_candidates.contains(&c))
                .count();
            if count < best_count {
                best_count = count;
                best_attacker = Some(b);
            }
        }
    }

    let b = best_attacker
        .expect("a non-self-defending node must have an undefeated attacker");

    af.attackers(b)
        .filter(|&c| !node.is_prohibited(*c) && !prohibited_candidates.contains(c))
        .copied()
        .collect()
}

/// Decide DC-CO: is `arg` credulously accepted with respect to the complete
/// semantics? Returns the complete extension of `af` containing `arg` if one
/// exists, `None` otherwise. If `verbose`, prints search-tree size
/// diagnostics (nodes visited, pseudo_complete calls) to stderr as it runs
/// -- useful for investigating slow instances.
pub fn dc_co(af: &AF, arg: usize, verbose: bool) -> Option<HashSet<usize>> {
    let mut nodes_visited: usize = 0;
    let mut pseudo_complete_calls: usize = 0;

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

    pseudo_complete_calls += 1;
    if !pseudo_complete(update, &mut current_node, af, &HashSet::new()) {
        // The hypothesis that `arg` is in the extension is already
        // contradictory: closing it produced a conflict.
        if verbose {
            eprintln!("[dc_co stats] nodes_visited={nodes_visited} pseudo_complete_calls={pseudo_complete_calls}");
        }
        return None;
    }

    if current_node.is_self_defending() {
        // node_args is conflict-free (checked above) and closed under
        // defense (guaranteed by pseudo_complete), and now every argument
        // in it defends itself: that's exactly a complete extension.
        if verbose {
            eprintln!("[dc_co stats] nodes_visited={nodes_visited} pseudo_complete_calls={pseudo_complete_calls}");
        }
        return Some(current_node.arguments());
    }

    // No candidate has been tried yet, so nothing is prohibited beyond what
    // conflicts_with already rejects dynamically.
    let prohibited_candidates = HashSet::new();
    let root_candidates = candidates(&current_node, af, &prohibited_candidates);
    let mut stack: Vec<Frame> = vec![Frame {
        node: current_node,
        candidates: root_candidates,
        prohibited_candidates,
        pending_candidate: None,
    }];

    while let Some(mut frame) = stack.pop() {
        nodes_visited += 1;
        if verbose && nodes_visited % 1000 == 0 {
            eprintln!(
                "[dc_co progress] nodes_visited={nodes_visited} pseudo_complete_calls={pseudo_complete_calls} stack_len={}",
                stack.len()
            );
        }

        // If set, the candidate's whole subtree just failed (see
        // pending_candidate's doc comment): it must never be retried in
        // this branch, even as a side effect of a different candidate's
        // closure.
        if let Some(failed) = frame.pending_candidate.take() {
            frame.prohibited_candidates.insert(failed);
        }

        // Take just one untried candidate; leave the rest for later, so a
        // sibling is only ever generated once this candidate's whole
        // subtree has been fully explored and abandoned.
        let Some(c) = frame.candidates.pop() else {
            continue;
        };

        let mut child = frame.node.clone();
        let child_prohibited_candidates = frame.prohibited_candidates.clone();

        // Push this frame back before trying c, regardless of outcome: if c
        // fails immediately, we'll pop it again right away; if it needs a
        // subtree, that gets pushed on top of it next.
        frame.pending_candidate = Some(c);
        stack.push(frame);

        pseudo_complete_calls += 1;
        if pseudo_complete(vec![c], &mut child, af, &child_prohibited_candidates) {
            if child.is_self_defending() {
                if verbose {
                    eprintln!("[dc_co stats] nodes_visited={nodes_visited} pseudo_complete_calls={pseudo_complete_calls}");
                }
                return Some(child.arguments());
            }
            let child_candidates = candidates(&child, af, &child_prohibited_candidates);
            stack.push(Frame {
                node: child,
                candidates: child_candidates,
                prohibited_candidates: child_prohibited_candidates,
                pending_candidate: None,
            });
        }
    }

    if verbose {
        eprintln!("[dc_co stats] nodes_visited={nodes_visited} pseudo_complete_calls={pseudo_complete_calls}");
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
        let extension = dc_co(&af, 0, false).expect("0 has no attackers, must be accepted");
        assert!(extension.contains(&0));
    }

    #[test]
    fn test_dc_co_none() {
        // Odd cycle 0 -> 1 -> 2 -> 0: no complete extension can contain 0.
        let mut af = AF::new(3);
        af.add_attack(0, 1);
        af.add_attack(1, 2);
        af.add_attack(2, 0);
        assert!(dc_co(&af, 0, false).is_none());
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

        let extension = dc_co(&af, 0, false).expect("1 can be defeated by either 2 or 3");
        assert!(extension.contains(&0));
        assert!(extension.contains(&2) || extension.contains(&3));
        assert!(!(extension.contains(&2) && extension.contains(&3)));
    }

    #[test]
    fn test_candidates_excludes_prohibited() {
        // 0 attacks the target 1's... wait, 1 attacks 0; both 2 and 3 attack
        // 1. If 3 is already known-prohibited (e.g. a previously-failed
        // candidate elsewhere in this branch), it must not be offered again
        // as a candidate to defeat 1.
        let mut af = AF::new(4);
        af.add_attack(1, 0);
        af.add_attack(2, 1);
        af.add_attack(3, 1);
        let mut node = Node::new(&af);
        assert!(pseudo_complete(vec![0], &mut node, &af, &HashSet::new()));

        let prohibited = HashSet::from([3]);
        assert_eq!(candidates(&node, &af, &prohibited), vec![2]);
    }
}
