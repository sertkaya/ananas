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
    // The candidate whose subtree we just pushed on top of this frame, if
    // any. If this frame is popped again while this is set, that subtree
    // must have failed entirely without success (a success would have
    // returned from the whole search already), so the candidate belongs in
    // prohibited_candidates before we try anything else from this frame.
    pending_candidate: Option<usize>,
}

/// Among `node`'s undefended members' undefeated attackers, find the one
/// with the fewest usable attackers of its own -- the most constrained
/// argument to defeat -- and return those attackers as the candidates to
/// try defeating it with. A candidate is usable when it is not already
/// decided, not in `prohibited_candidates`, and does not conflict with the
/// set; that is the candidate set `C ⊆ A \ (R(S) ∪ R⁻¹(S) ∪ P)` of the
/// paper's Algorithm 1, and the same predicate has to be used for the
/// counting, since selecting the smallest candidate set is only meaningful
/// if unusable candidates are excluded from the counts too.
///
/// Conflicting arguments need no scan to find: `Node::known_defeated` is
/// set exactly for `R(S)` by the semi-complete loop and for `R⁻¹(S)` by the
/// quasi-complete loop, so once `pseudo_complete` has returned it *is*
/// `R(S) ∪ R⁻¹(S)`. Only the self-attackers have to be supplied separately,
/// in `self_attacking`, since they are a property of the framework rather
/// than of the node (the paper puts them in the initial `P` instead).
///
/// Candidates are ordered so that the one with the fewest attackers of its
/// own (hence the least likely to trigger further branching) is tried
/// first, with ties broken by argument id. Both the search over undefeated
/// attackers and this ordering are made fully deterministic on purpose:
/// af.attackers()/af.victims() iterate a HashSet, whose order depends on
/// Rust's per-process randomized hash seed, so leaving either choice to
/// that order would make the amount of search work done for the exact same
/// query vary randomly from run to run.
///
/// `node` must not be self-defending, i.e. some member must have an
/// undefeated attacker.
fn candidates(node: &Node, af: &AF, self_attacking: &[bool]) -> Vec<usize> {
    let usable = |c: usize| {
        !node.is_out(c) && !node.known_defeated(c) && !self_attacking[c]
    };

    let mut best_attacker: Option<usize> = None;
    let mut best_count = usize::MAX;
    for m in 0..af.argument_count() {
        if !node.contains(m) || node.unattacked_attackers_count(m) == 0 {
            continue;
        }
        for &b in af.attackers(m) {
            // Equivalent to node.is_defeated(af, b), but O(1): the
            // semi-complete loop sets defeat_propagated for exactly the
            // arguments some member attacks, and pseudo_complete has
            // drained its worklist by the time we get here. Worth the
            // indirection -- this runs for every attacker of every
            // undefended member, and is_defeated walks an attacker set.
            if node.defeat_propagated(b) {
                continue;
            }
            let count = af.attackers(b).filter(|&&c| usable(c)).count();
            let better = match best_attacker {
                None => true,
                Some(current) => count < best_count || (count == best_count && b < current),
            };
            if better {
                best_count = count;
                best_attacker = Some(b);
            }
        }
    }

    let b = best_attacker
        .expect("a non-self-defending node must have an undefeated attacker");

    let mut result: Vec<usize> = af.attackers(b)
        .filter(|&&c| usable(c))
        .copied()
        .collect();
    result.sort_by_key(|&c| (af.attacker_count(c), c));
    result.reverse();
    result
}

/// Format the diagnostic counters tracked by `dc_co` for a `verbose` print.
fn format_stats(
    nodes_visited: usize,
    pseudo_complete_calls: usize,
    frames_created: usize,
    candidate_count_sum: usize,
    candidate_count_min: usize,
    candidate_count_max: usize,
) -> String {
    let avg = if frames_created > 0 {
        candidate_count_sum as f64 / frames_created as f64
    } else {
        0.0
    };
    let min = if frames_created > 0 { candidate_count_min } else { 0 };
    format!(
        "nodes_visited={nodes_visited} pseudo_complete_calls={pseudo_complete_calls} \
         frames_created={frames_created} candidates_avg={avg:.2} \
         candidates_min={min} candidates_max={candidate_count_max}"
    )
}

/// Decide DC-CO: is `arg` credulously accepted with respect to the complete
/// semantics? Returns the complete extension of `af` containing `arg` if one
/// exists, `None` otherwise. If `verbose`, prints search-tree size
/// diagnostics (nodes visited, pseudo_complete calls) to stderr as it runs
/// -- useful for investigating slow instances.
pub fn dc_co(af: &AF, arg: usize, verbose: bool) -> Option<HashSet<usize>> {
    let mut nodes_visited: usize = 0;
    let mut pseudo_complete_calls: usize = 0;
    // Distribution of candidates.len() at every frame creation (root and
    // children), to see whether difficulty comes from many nodes each
    // having a handful of candidates, or a few nodes with huge candidate
    // lists.
    let mut frames_created: usize = 0;
    let mut candidate_count_sum: usize = 0;
    let mut candidate_count_max: usize = 0;
    let mut candidate_count_min: usize = usize::MAX;

    // Self-attacking arguments can never belong to a conflict-free set, so
    // they are never usable candidates. This depends only on the framework,
    // not on the search state, so it is computed once here rather than per
    // node (the paper folds it into the initial prohibited set instead).
    let self_attacking: Vec<bool> = (0..af.argument_count()).map(|a| af.attacks(a, a)).collect();

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
    if !pseudo_complete(update, &mut current_node, af) {
        // The hypothesis that `arg` is in the extension is already
        // contradictory: closing it produced a conflict.
        if verbose {
            eprintln!(
                "[dc_co stats] {}",
                format_stats(
                    nodes_visited,
                    pseudo_complete_calls,
                    frames_created,
                    candidate_count_sum,
                    candidate_count_min,
                    candidate_count_max
                )
            );
        }
        return None;
    }

    if current_node.is_self_defending() {
        // node_args is conflict-free (checked above) and closed under
        // defense (guaranteed by pseudo_complete), and now every argument
        // in it defends itself: that's exactly a complete extension.
        if verbose {
            eprintln!(
                "[dc_co stats] {}",
                format_stats(
                    nodes_visited,
                    pseudo_complete_calls,
                    frames_created,
                    candidate_count_sum,
                    candidate_count_min,
                    candidate_count_max
                )
            );
        }
        return Some(current_node.arguments());
    }

    let root_candidates = candidates(&current_node, af, &self_attacking);
    frames_created += 1;
    candidate_count_sum += root_candidates.len();
    candidate_count_max = candidate_count_max.max(root_candidates.len());
    candidate_count_min = candidate_count_min.min(root_candidates.len());
    let mut stack: Vec<Frame> = vec![Frame {
        node: current_node,
        candidates: root_candidates,
        pending_candidate: None,
    }];

    while let Some(mut frame) = stack.pop() {
        nodes_visited += 1;
        if verbose && nodes_visited.is_multiple_of(1000) {
            eprintln!(
                "[dc_co progress] {} stack_len={}",
                format_stats(
                    nodes_visited,
                    pseudo_complete_calls,
                    frames_created,
                    candidate_count_sum,
                    candidate_count_min,
                    candidate_count_max
                ),
                stack.len()
            );
        }

        // If set, the candidate's whole subtree just failed (see
        // pending_candidate's doc comment): it must never be retried in
        // this branch, even as a side effect of a different candidate's
        // closure.
        if let Some(failed) = frame.pending_candidate.take() {
            frame.node.rule_out(failed);
        }

        // Take just one untried candidate; leave the rest for later, so a
        // sibling is only ever generated once this candidate's whole
        // subtree has been fully explored and abandoned.
        let Some(c) = frame.candidates.pop() else {
            continue;
        };

        // The out-set rides along inside the node, so this one clone
        // carries the whole partial assignment to the child.
        let mut child = frame.node.clone();

        // Push this frame back before trying c, regardless of outcome: if c
        // fails immediately, we'll pop it again right away; if it needs a
        // subtree, that gets pushed on top of it next.
        frame.pending_candidate = Some(c);
        stack.push(frame);

        pseudo_complete_calls += 1;
        if pseudo_complete(vec![c], &mut child, af) {
            if child.is_self_defending() {
                if verbose {
                    eprintln!(
                "[dc_co stats] {}",
                format_stats(
                    nodes_visited,
                    pseudo_complete_calls,
                    frames_created,
                    candidate_count_sum,
                    candidate_count_min,
                    candidate_count_max
                )
            );
                }
                return Some(child.arguments());
            }
            let child_candidates = candidates(&child, af, &self_attacking);
            frames_created += 1;
            candidate_count_sum += child_candidates.len();
            candidate_count_max = candidate_count_max.max(child_candidates.len());
            candidate_count_min = candidate_count_min.min(child_candidates.len());
            stack.push(Frame {
                node: child,
                candidates: child_candidates,
                pending_candidate: None,
            });
        }
    }

    if verbose {
        eprintln!(
            "[dc_co stats] {}",
            format_stats(
                nodes_visited,
                pseudo_complete_calls,
                frames_created,
                candidate_count_sum,
                candidate_count_min,
                candidate_count_max
            )
        );
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
    fn test_candidates_excludes_ruled_out() {
        // 1 attacks the target 0; 2, 3 and 4 all attack 1. If 4 has been
        // ruled out (e.g. its subtree already failed higher in this branch)
        // it must not be offered again as a candidate for defeating 1.
        // Three attackers rather than two, so that ruling one out still
        // leaves a genuine choice -- with only one survivor the
        // single-defender rule would resolve 1 inside the closure and there
        // would be nothing left to select.
        let mut af = AF::new(5);
        af.add_attack(1, 0);
        af.add_attack(2, 1);
        af.add_attack(3, 1);
        af.add_attack(4, 1);
        let mut node = Node::new(&af);
        node.rule_out(4);
        assert!(pseudo_complete(vec![0], &mut node, &af));

        let self_attacking = vec![false; af.argument_count()];
        let result = candidates(&node, &af, &self_attacking);
        assert!(!result.contains(&4), "4 was ruled out for this branch");
        // Both survivors are unattacked, so they tie on attacker count and
        // order by id -- reversed, since the search pops from the back.
        assert_eq!(result, vec![3, 2]);
    }

    #[test]
    fn test_candidates_excludes_conflicting() {
        // 1 attacks the target 0 and must be defeated. Its attackers 2, 3
        // and 4 are the would-be defenders, but 2 is itself attacked by 0,
        // so it conflicts with the set and could never be added -- the
        // paper's Algorithm 1 forms its candidates from
        // A \ (R(S) ∪ R⁻¹(S) ∪ P), so 2 must not be offered. 3 and 4 both
        // stay available, which also keeps the single-defender rule from
        // resolving 1 on its own.
        let mut af = AF::new(5);
        af.add_attack(1, 0);
        af.add_attack(2, 1);
        af.add_attack(3, 1);
        af.add_attack(4, 1);
        af.add_attack(0, 2);
        let mut node = Node::new(&af);
        assert!(pseudo_complete(vec![0], &mut node, &af));

        let self_attacking = vec![false; af.argument_count()];
        let result = candidates(&node, &af, &self_attacking);
        assert!(!result.contains(&2), "2 is attacked by the set, so it can never be added");
        // Both remaining candidates are unattacked, so they tie on attacker
        // count and order by id -- reversed, since the search pops from the back.
        assert_eq!(result, vec![4, 3]);
    }
}
