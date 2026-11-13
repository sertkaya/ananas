use std::collections::HashSet;
use crate::af::AF;
use crate::algorithms::closure::{backtrack, pseudo_complete, rule_out};
use crate::algorithms::node::{Node, Value};

/// A node of the search tree: where its assignments start on the search's
/// trail, and the candidate arguments still to be tried, lazily, for
/// defeating its most constrained undefeated attacker. The arguments
/// already known (from earlier failed candidates tried at or above this
/// point) to be unsuitable for this branch are out on the trail.
struct Frame {
    // Length of the trail before this frame's own decision, so that
    // backtracking to it undoes the frame entirely
    start: usize,
    candidates: Vec<usize>,
    // The candidate whose subtree we just pushed on top of this frame, if
    // any. If this frame is popped again while this is set, that subtree
    // must have failed entirely without success (a success would have
    // returned from the whole search already), so the candidate is ruled
    // out of the node before we try anything else from this frame.
    pending_candidate: Option<usize>,
}

/// Among `node`'s undefended members' undefeated attackers, find the one
/// with the fewest usable attackers of its own -- the most constrained
/// argument to defeat -- and return those attackers as the candidates to
/// try defeating it with. A candidate is usable when it is still
/// undecided; that is the candidate set `C ⊆ A \ (R(S) ∪ R⁻¹(S) ∪ P)` of
/// the paper's Algorithm 1, since once `pseudo_complete` has returned the
/// out arguments are exactly the ones that conflict with the set, attack
/// themselves, or have been ruled out. The same predicate has to be used
/// for the counting, since selecting the smallest candidate set is only
/// meaningful if unusable candidates are excluded from the counts too.
///
/// Candidates are ordered so that the one with the fewest attackers of its
/// own (hence the least likely to trigger further branching) is tried
/// first, with ties broken by argument id. Both the search over undefeated
/// attackers and this ordering break ties explicitly by id rather than
/// leaving them to adjacency order, so that the amount of search work done
/// for a query does not depend on how the framework happens to be stored.
///
/// `node` must not be self-defending, i.e. some member must have an
/// undefeated attacker.
fn candidates(node: &Node, af: &AF) -> Vec<usize> {
    let usable = |c: usize| node.value(c) == Value::Undecided;

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
            // Maintained incrementally by the closure, so this is a read
            // rather than a scan of b's attackers.
            let count = node.usable_defenders_count(b);
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
    empty_candidate_lists: usize,
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
         candidates_min={min} candidates_max={candidate_count_max} \
         empty_candidate_lists={empty_candidate_lists}"
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
    // How often candidates() came back empty: the branch was already dead,
    // but pseudo_complete did not notice, so we paid a full candidate scan
    // to find out. Measures what the once-per-attacker no-defender check
    // misses.
    let mut empty_candidate_lists: usize = 0;

    let mut node = Node::new(af);

    // We hypothesize that `arg` is in the extension, and arguments with no
    // attackers are defended by default, so both are seeds; pseudo_complete
    // adds them to `node` before propagating their effects.
    let mut seeds = vec![arg];
    for a in 0..af.argument_count() {
        if af.attacker_count(a) == 0 {
            seeds.push(a);
        }
    }

    pseudo_complete_calls += 1;
    if !pseudo_complete(seeds, &mut node, af) {
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
                    candidate_count_max,
                    empty_candidate_lists
                )
            );
        }
        return None;
    }

    if node.is_self_defending() {
        // The set is conflict-free (checked above) and closed under
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
                    candidate_count_max,
                    empty_candidate_lists
                )
            );
        }
        return Some(node.arguments());
    }

    let root_candidates = candidates(&node, af);
    if root_candidates.is_empty() {
        empty_candidate_lists += 1;
    }
    frames_created += 1;
    candidate_count_sum += root_candidates.len();
    candidate_count_max = candidate_count_max.max(root_candidates.len());
    candidate_count_min = candidate_count_min.min(root_candidates.len());
    let mut stack: Vec<Frame> = vec![Frame {
        start: 0,
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
                    candidate_count_max,
                    empty_candidate_lists
                ),
                stack.len()
            );
        }

        // If set, the candidate's whole subtree just failed (see
        // pending_candidate's doc comment): it must never be retried in
        // this branch, even as a side effect of a different candidate's
        // closure.
        // If ruling it out leaves the node itself contradictory, no
        // remaining candidate can succeed from here either, so the whole
        // frame fails at once instead of sibling by sibling.
        // Either way the frame is then done with, and is undone.
        if let Some(failed) = frame.pending_candidate.take()
            && !rule_out(failed, &mut node, af)
        {
            backtrack(frame.start, &mut node, af);
            continue;
        }

        // Take just one untried candidate; leave the rest for later, so a
        // sibling is only ever generated once this candidate's whole
        // subtree has been fully explored and abandoned.
        let Some(c) = frame.candidates.pop() else {
            backtrack(frame.start, &mut node, af);
            continue;
        };

        // Push this frame back before trying c, regardless of outcome: if c
        // fails immediately, we'll pop it again right away; if it needs a
        // subtree, that gets pushed on top of it next.
        frame.pending_candidate = Some(c);
        stack.push(frame);

        let child_start = node.trail_len();
        pseudo_complete_calls += 1;
        if !pseudo_complete(vec![c], &mut node, af) {
            backtrack(child_start, &mut node, af);
        } else {
            if node.is_self_defending() {
                if verbose {
                    eprintln!(
                "[dc_co stats] {}",
                format_stats(
                    nodes_visited,
                    pseudo_complete_calls,
                    frames_created,
                    candidate_count_sum,
                    candidate_count_min,
                    candidate_count_max,
                    empty_candidate_lists
                )
            );
                }
                return Some(node.arguments());
            }
            let child_candidates = candidates(&node, af);
            if child_candidates.is_empty() {
                empty_candidate_lists += 1;
            }
            frames_created += 1;
            candidate_count_sum += child_candidates.len();
            candidate_count_max = candidate_count_max.max(child_candidates.len());
            candidate_count_min = candidate_count_min.min(child_candidates.len());
            stack.push(Frame {
                start: child_start,
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
                candidate_count_max,
                empty_candidate_lists
            )
        );
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::random_af::{random_af, Rng};

    // dc_co agrees with brute force on random small frameworks: it answers
    // YES exactly when some complete extension contains the argument, and
    // the extension it returns is complete and contains it.
    #[test]
    fn test_dc_co_matches_brute_force() {
        let mut rng = Rng::new(2);
        for round in 0..400 {
            let n = 2 + rng.below(9);
            let percent = [10, 20, 35, 50][rng.below(4)];
            let af = random_af(&mut rng, n, percent);
            let complete: Vec<HashSet<usize>> = (0..1u32 << n)
                .map(|bits| (0..n).filter(|&a| bits & (1 << a) != 0).collect())
                .filter(|set| af.is_complete(set))
                .collect();
            for arg in 0..n {
                let expected = complete.iter().any(|set| set.contains(&arg));
                match dc_co(&af, arg, false) {
                    Some(extension) => {
                        assert!(expected, "round {round}, arg {arg}: YES, but no complete extension contains it\n{af}");
                        assert!(extension.contains(&arg) && af.is_complete(&extension),
                            "round {round}, arg {arg}: returned {extension:?}, not a complete extension containing it\n{af}");
                    }
                    None => assert!(!expected, "round {round}, arg {arg}: NO, but a complete extension contains it\n{af}"),
                }
            }
        }
    }

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
        assert!(rule_out(4, &mut node, &af));
        assert!(pseudo_complete(vec![0], &mut node, &af));

        let result = candidates(&node, &af);
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

        let result = candidates(&node, &af);
        assert!(!result.contains(&2), "2 is attacked by the set, so it can never be added");
        // Both remaining candidates are unattacked, so they tie on attacker
        // count and order by id -- reversed, since the search pops from the back.
        assert_eq!(result, vec![4, 3]);
    }
}
