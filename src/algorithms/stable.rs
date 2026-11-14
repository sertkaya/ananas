//! Stable semantics: DC-ST and SE-ST.

use std::collections::HashSet;
use crate::af::AF;
use crate::algorithms::lit::Semantics;
use crate::algorithms::search::Solver;

/// Decide DC-ST: is `arg` credulously accepted with respect to the stable
/// semantics? Returns a stable extension of `af` containing `arg` if one
/// exists, `None` otherwise. If `verbose`, prints search diagnostics to
/// stderr.
pub fn dc_st(af: &AF, arg: usize, verbose: bool) -> Option<HashSet<usize>> {
    let mut solver = Solver::new(af, Semantics::Stable, verbose);
    let result = solver.solve(&[arg]);
    if verbose {
        eprintln!("[dc_st stats] {}", solver.stats());
    }
    result
}

/// Solve SE-ST: return some stable extension of `af`, or `None` if it has
/// none. If `verbose`, prints search diagnostics to stderr.
pub fn se_st(af: &AF, verbose: bool) -> Option<HashSet<usize>> {
    let mut solver = Solver::new(af, Semantics::Stable, verbose);
    let result = solver.solve(&[]);
    if verbose {
        eprintln!("[se_st stats] {}", solver.stats());
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::random_af::{random_af, Rng};

    /// Every stable extension of `af`, by brute force
    fn stable_extensions(af: &AF) -> Vec<HashSet<usize>> {
        let n = af.argument_count();
        (0..1u32 << n)
            .map(|bits| (0..n).filter(|&a| bits & (1 << a) != 0).collect())
            .filter(|set| af.is_stable(set))
            .collect()
    }

    #[test]
    fn test_dc_st_even_cycle() {
        // 0 <-> 1: both {0} and {1} are stable
        let mut af = AF::new(2);
        af.add_attack(0, 1);
        af.add_attack(1, 0);
        assert_eq!(dc_st(&af, 0, false), Some(HashSet::from([0])));
        assert_eq!(dc_st(&af, 1, false), Some(HashSet::from([1])));
    }

    #[test]
    fn test_dc_st_odd_cycle_blocks_stability() {
        // 0 is unattacked, so it is in every complete extension, but the odd
        // cycle 1 -> 2 -> 3 -> 1 leaves no way to attack every outsider
        let mut af = AF::new(4);
        af.add_attack(1, 2);
        af.add_attack(2, 3);
        af.add_attack(3, 1);
        assert!(dc_st(&af, 0, false).is_none());
        assert!(se_st(&af, false).is_none());
    }

    // dc_st and se_st agree with brute force on random small frameworks:
    // dc_st answers YES exactly when some stable extension contains the
    // argument, se_st exactly when there is one at all, and what either
    // returns is stable.
    #[test]
    fn test_stable_matches_brute_force() {
        let mut rng = Rng::new(8);
        let mut yes = 0;
        for round in 0..600 {
            let n = 2 + rng.below(9);
            let percent = [10, 20, 35, 50][rng.below(4)];
            let af = random_af(&mut rng, n, percent);
            let stable = stable_extensions(&af);
            match se_st(&af, false) {
                Some(extension) => {
                    assert!(af.is_stable(&extension), "round {round}: {extension:?} is not stable\n{af}");
                    yes += 1;
                }
                None => assert!(stable.is_empty(), "round {round}: NO, but {:?} is stable\n{af}", stable[0]),
            }
            for arg in 0..n {
                let expected = stable.iter().any(|set| set.contains(&arg));
                match dc_st(&af, arg, false) {
                    Some(extension) => {
                        assert!(expected, "round {round}, arg {arg}: YES, but no stable extension contains it\n{af}");
                        assert!(extension.contains(&arg) && af.is_stable(&extension),
                            "round {round}, arg {arg}: returned {extension:?}, not a stable extension containing it\n{af}");
                    }
                    None => assert!(!expected, "round {round}, arg {arg}: NO, but a stable extension contains it\n{af}"),
                }
            }
        }
        assert!(yes > 100, "too few frameworks with a stable extension ({yes})");
    }
}
