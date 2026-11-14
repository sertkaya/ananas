//! Complete semantics: DC-CO.

use std::collections::HashSet;
use crate::af::AF;
use crate::algorithms::lit::Semantics;
use crate::algorithms::search::Solver;

/// Decide DC-CO: is `arg` credulously accepted with respect to the complete
/// semantics? Returns the complete extension of `af` containing `arg` if one
/// exists, `None` otherwise. If `verbose`, prints search diagnostics
/// (decisions, conflicts, learned clauses) to stderr as it runs -- useful
/// for investigating slow instances.
pub fn dc_co(af: &AF, arg: usize, verbose: bool) -> Option<HashSet<usize>> {
    let mut solver = Solver::new(af, Semantics::Complete, verbose);
    let result = solver.solve(&[arg]);
    if verbose {
        eprintln!("[dc_co stats] {}", solver.stats());
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::random_af::{random_af, Rng};

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
}
