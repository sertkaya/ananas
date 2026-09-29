use std::collections::HashSet;
use crate::af::AF;
use crate::algorithms::node::Node;

/// Extend `node` with its smallest pseudo-complete superset.
///
/// Both closure rules rest on the same observation: an argument `b` is
/// defeated in *every* complete extension containing `node`'s current
/// arguments as soon as either a member attacks `b` (semi-complete) or `b`
/// attacks a member, since a complete extension defends its members and so
/// must attack `b` back (quasi-complete). Once all of some argument's
/// attackers are known defeated that way, it is defended in every
/// completion and is added, whether or not it is defended *yet*.
///
/// The two routes therefore share one counter, so an argument whose
/// attackers are covered by a mixture of them is still forced -- which two
/// separate per-rule counters would miss.
///
/// The rules are applied repeatedly until neither can add anything more.
/// `update` is a stack of arguments to add to `node` and whose effect on
/// their attacked arguments' victims (semi-complete) and their attackers'
/// other victims (quasi-complete) still needs to be propagated.
/// `prohibited_candidates` are arguments already known to be unsuitable
/// (e.g. previously-failed search candidates in this branch); the closure
/// must not be forced to include any of them.
///
/// Returns `false` as soon as an argument that would be added conflicts with
/// `node`'s current set (in either attack direction, including self-attack)
/// or is in `prohibited_candidates`, leaving `node` in a discarded,
/// no-longer-meaningful state. Returns `true` if the closure completed
/// without any conflict.
#[must_use]
pub fn pseudo_complete(
    mut update: Vec<usize>,
    node: &mut Node,
    af: &AF,
    prohibited_candidates: &HashSet<usize>,
) -> bool {
    // Mark the seed arguments as added up front, before any propagation, so
    // that a seed sitting deeper on the stack is already prohibited if some
    // other seed's propagation happens to target it first.
    for &arg in &update {
        if node.conflicts_with(af, arg) || prohibited_candidates.contains(&arg) {
            return false;
        }
        node.add_argument(arg);
    }

    while let Some(arg) = update.pop() {
        // --- begin: semi-complete closure ---
        for &victim in af.victims(arg) {
            // A member of the set attacks `victim`, so `victim` is defeated
            // outright. Two separate facts follow, each propagated at most
            // once: that it is *actually* defeated by the set so far (which
            // feeds the defended-check used by is_self_defending and
            // candidates), and that it is defeated in *every* completion
            // (which drives forcing, and may already be known because it
            // attacks a member -- see the quasi-complete rule below).
            // Propagating either twice would double-count this one attacker
            // against its victims' counts.
            let first_defeat = !node.defeat_propagated(victim);
            let first_known = !node.known_defeated(victim);
            if !first_defeat && !first_known {
                continue;
            }
            if first_defeat {
                node.mark_defeat_propagated(victim);
            }
            if first_known {
                node.mark_known_defeated(victim);
            }

            for &victim_of_victim in af.victims(victim) {
                // No is_prohibited guard here: the flags above already
                // ensure each real attacker of victim_of_victim contributes
                // at most one decrement to each counter (deduplicated per
                // attacker, not per target), so neither can be called more
                // times than victim_of_victim's original attacker count --
                // including for forced/seeded arguments, whose counts must
                // keep being updated after they're already in the set.
                if first_defeat {
                    node.decrement_unattacked_attackers(victim_of_victim);
                }
                if first_known
                    && node.decrement_undefeated_attackers(victim_of_victim) == 0
                {
                    if node.conflicts_with(af, victim_of_victim)
                        || prohibited_candidates.contains(&victim_of_victim)
                    {
                        return false;
                    }
                    node.add_argument(victim_of_victim);
                    update.push(victim_of_victim);
                }
            }
        }
        // --- end: semi-complete closure ---

        // --- begin: quasi-complete closure ---
        for &attacker in af.attackers(arg) {
            // `attacker` attacks a member of the set. A complete extension
            // must defend its members, so any completion attacks `attacker`
            // back: it too is defeated in every completion. That is the same
            // fact the semi-complete rule above establishes by the other
            // route, so it shares the flag -- whichever route reaches an
            // argument first, the second must not decrement again.
            if node.known_defeated(attacker) {
                continue;
            }
            node.mark_known_defeated(attacker);

            // --- begin: single-attacker (P-pseudo-complete) optimization ---
            // Section 4.2 of the paper: if `attacker` is an undefeated
            // attacker of the set with exactly one remaining possible
            // defender, that defender is forced -- there's no alternative
            // to branch on, so add it right here instead of waiting for
            // the search to discover and try it as a single-candidate
            // branch.
            if !node.is_defeated(af, attacker) {
                let remaining: Vec<usize> = af.attackers(attacker)
                    .filter(|&&b| {
                        !node.is_prohibited(b)
                            && !prohibited_candidates.contains(&b)
                            && !node.conflicts_with(af, b)
                    })
                    .copied()
                    .collect();
                if remaining.is_empty() {
                    // `attacker` attacks the set, nothing in the set
                    // defeats it, and every one of its own attackers is
                    // prohibited or conflicts with the set. The set can
                    // never be defended against it, so this branch is
                    // already dead. Saying so here saves the search a
                    // candidate scan that could only return an empty list.
                    return false;
                }
                if remaining.len() == 1 {
                    node.add_argument(remaining[0]);
                    update.push(remaining[0]);
                }
            }
            // --- end: single-attacker (P-pseudo-complete) optimization ---

            for &co_victim in af.victims(attacker) {
                if node.decrement_undefeated_attackers(co_victim) == 0 {
                    if node.conflicts_with(af, co_victim)
                        || prohibited_candidates.contains(&co_victim)
                    {
                        return false;
                    }
                    node.add_argument(co_victim);
                    update.push(co_victim);
                }
            }
        }
        // --- end: quasi-complete closure ---
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

        assert!(pseudo_complete(vec![0], &mut node, &af, &HashSet::new()));

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

        assert!(pseudo_complete(update, &mut node, &af, &HashSet::new()));

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

        assert!(pseudo_complete(vec![0], &mut node, &af, &HashSet::new()));

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

        assert!(!pseudo_complete(vec![0], &mut node, &af, &HashSet::new()));
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

        assert!(pseudo_complete(vec![0, 1], &mut node, &af, &HashSet::new()));

        println!("{}", node);
        assert!(!node.contains(3), "3's attacker 4 was never defeated");
    }

    // 0 -> 1 -> 2: forcing 0 in organically pulls in 2 (via 1's defeat), with
    // no direct conflict. If 2 is already a known-prohibited candidate (e.g.
    // a previously-failed search hypothesis), the closure must still reject
    // it, even though nothing here would trip conflicts_with on its own.
    #[test]
    fn test_pseudo_complete_prohibited_candidate() {
        let mut af = AF::new(3);
        af.add_attack(0, 1);
        af.add_attack(1, 2);
        let mut node = Node::new(&af);

        assert!(!pseudo_complete(vec![0], &mut node, &af, &HashSet::from([2])));
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
        let mut node = Node::new(&af);

        assert!(pseudo_complete(vec![0], &mut node, &af, &HashSet::new()));

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
        let mut node = Node::new(&af);

        assert!(!pseudo_complete(vec![0], &mut node, &af, &HashSet::new()));
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
        let mut node = Node::new(&af);

        assert!(pseudo_complete(vec![0], &mut node, &af, &HashSet::new()));

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
        let mut node = Node::new(&af);

        assert!(pseudo_complete(vec![0], &mut node, &af, &HashSet::new()));

        println!("{}", node);
        assert!(node.contains(2), "2 is 1's only possible defender");
        assert!(node.contains(4), "4 is 3's only possible defender");
        assert!(node.is_self_defending());
    }
}
