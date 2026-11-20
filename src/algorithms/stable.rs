//! Stable semantics: DC-ST and SE-ST.

use std::collections::HashSet;
use crate::af::AF;
use crate::algorithms::lit::Semantics;
use crate::algorithms::search::{Order, Outcome, Solver};

/// Decide DC-ST: is `arg` credulously accepted with respect to the stable
/// semantics? Returns a stable extension of `af` containing `arg` if one
/// exists, `None` otherwise. If `verbose`, prints search diagnostics to
/// stderr.
pub fn dc_st(af: &AF, arg: usize, verbose: bool) -> Option<HashSet<usize>> {
    portfolio(af, &[arg], SLICE, Order::Topological, verbose, "dc_st").0
}

/// Solve SE-ST: return some stable extension of `af`, or `None` if it has
/// none. If `verbose`, prints search diagnostics to stderr.
pub fn se_st(af: &AF, verbose: bool) -> Option<HashSet<usize>> {
    portfolio(af, &[], SLICE, Order::Topological, verbose, "se_st").0
}

// The propagation work each search of the portfolio gets per turn, about
// a tenth of a second
const SLICE: usize = 50_000_000;
// With a strongly connected component this large a share of the
// framework, the topological order is the activity order, and the
// portfolio would run the same search twice
const ONE_COMPONENT: f64 = 0.9;

/// Find a stable extension containing `assumptions` with two searches
/// taking turns in one thread: one deciding in topological order, one by
/// activity alone. Neither order wins everywhere -- building an extension
/// component by component wants the first, refuting a contradiction deep
/// in the framework the second -- and mixing them in one search spoiled
/// both. As separate searches, each with its own clauses, activities and
/// phases, resumed where it stopped, the pair costs at most about twice
/// the faster one.
///
/// The search in order `first` takes the first turn, so that queries it
/// settles within one turn never start the other one; the problems start
/// with the topological search. Each turn gets `slice` units of
/// propagation work: work, not conflicts, because a conflict can cost one
/// order twice what it costs the other. A search suspended at the end of
/// its turn resumes exactly where it stopped, so switching costs nothing,
/// and equal slices keep the total at about twice the faster search.
/// (Doubling slices, the usual schedule when switching costs a restart,
/// let the second search finish only after the first had spent up to
/// twice its time again: 3.1 times the activity search alone on
/// crusti_200_0.1_127_15 DC-ST.) (st_542 SE-ST, one component holding 94% of the
/// arguments, ran the identical search twice and timed out at 900s
/// instead of 62s; so a framework that is essentially one component gets
/// a single search.) Returns the answer and the order of the search that
/// found it.
fn portfolio(
    af: &AF,
    assumptions: &[usize],
    slice: usize,
    first: Order,
    verbose: bool,
    name: &str,
) -> (Option<HashSet<usize>>, Order) {
    let orders = match first {
        Order::Topological => [Order::Topological, Order::Activity],
        Order::Activity => [Order::Activity, Order::Topological],
    };
    let mut topological = Solver::with_order(af, Semantics::Stable, verbose, Order::Topological);
    if topological.largest_component_share() >= ONE_COMPONENT {
        let answer = topological.solve(assumptions);
        if verbose {
            eprintln!("[{name} portfolio] one component, a single search");
            eprintln!("[{name} stats] {}", topological.stats());
        }
        return (answer, Order::Topological);
    }
    // The other search is only made once the first has had a turn
    let mut searches: [Option<Solver>; 2] = match first {
        Order::Topological => [Some(topological), None],
        Order::Activity => [None, Some(topological)],
    };
    let (answer, winner) = 'rounds: loop {
        for (i, order) in orders.into_iter().enumerate() {
            let search = searches[i].get_or_insert_with(|| Solver::with_order(af, Semantics::Stable, verbose, order));
            match search.solve_limited(assumptions, slice) {
                Outcome::Extension(extension) => break 'rounds (Some(extension), order),
                Outcome::NoExtension => break 'rounds (None, order),
                Outcome::Unknown => {}
            }
        }
    };
    if verbose {
        eprintln!("[{name} portfolio] answered by the {winner:?} search");
        for (order, search) in orders.iter().zip(&searches) {
            if let Some(search) = search {
                eprintln!("[{name} stats, {order:?}] {}", search.stats());
            }
        }
    }
    (answer, winner)
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

    /// `af` with its arguments paired up in mutual attacks, 0 <-> 1,
    /// 2 <-> 3, ..., which keeps stable extensions common
    fn paired(mut af: AF) -> AF {
        let n = af.argument_count();
        for a in (0..n.saturating_sub(1)).step_by(2) {
            af.add_attack(a, a + 1);
            af.add_attack(a + 1, a);
        }
        af
    }

    // The portfolio with slices of a conflict or two agrees with brute
    // force. On frameworks this small almost every conflict learns a unit,
    // so slices rarely run out; the next test is where they do.
    #[test]
    fn test_portfolio_matches_brute_force() {
        let mut rng = Rng::new(13);
        for round in 0..300 {
            let n = 4 + rng.below(9);
            let percent = [10, 20, 35][rng.below(3)];
            let mut af = random_af(&mut rng, n, percent);
            if rng.below(2) == 1 {
                af = paired(af);
            }
            let stable = stable_extensions(&af);
            let slice = 1 + rng.below(2);
            for query in std::iter::once(None).chain((0..n).map(Some)) {
                let assumptions: Vec<usize> = query.into_iter().collect();
                let expected = stable.iter().any(|set| assumptions.iter().all(|a| set.contains(a)));
                let first = [Order::Topological, Order::Activity][rng.below(2)];
                match portfolio(&af, &assumptions, slice, first, false, "test").0 {
                    Some(extension) => {
                        assert!(expected, "round {round}, {assumptions:?}: YES wrongly\n{af}");
                        assert!(assumptions.iter().all(|a| extension.contains(a)) && af.is_stable(&extension),
                            "round {round}, {assumptions:?}: {extension:?}\n{af}");
                    }
                    None => assert!(!expected, "round {round}, {assumptions:?}: NO wrongly\n{af}"),
                }
            }
        }
    }

    /// `k` random components of `size` arguments each, attacks inside a
    /// component with probability `inner` percent, and from each component
    /// to every later one with probability `cross` percent: a framework
    /// whose strongly connected components come in a known order, like the
    /// crusti family in miniature
    fn layered(rng: &mut Rng, k: usize, size: usize, inner: usize, cross: usize) -> AF {
        let mut af = AF::new(k * size);
        for a in 0..k * size {
            for b in 0..k * size {
                let percent = match (a / size).cmp(&(b / size)) {
                    std::cmp::Ordering::Equal => inner,
                    std::cmp::Ordering::Less => cross,
                    std::cmp::Ordering::Greater => 0,
                };
                if rng.below(100) < percent {
                    af.add_attack(a, b);
                }
            }
        }
        af
    }

    // On frameworks of several components, with slices of a few
    // conflicts, the two searches hand over to each other, each resuming
    // where it stopped. Whichever search starts, and whichever answers, the
    // portfolio agrees with a single search run to the end, and what it
    // returns is stable. On frameworks this small the first search usually
    // answers -- it wins ties within a round -- so the first one is chosen
    // at random, and the second answers often enough only over many
    // queries.
    #[test]
    fn test_portfolio_keeps_answers() {
        let mut rng = Rng::new(15);
        let mut won = [0, 0];
        let mut second_answered = 0;
        let mut answers = [0, 0];
        for round in 0..600 {
            let k = 4 + rng.below(5);
            let size = 15 + rng.below(16);
            let (inner, cross) = (4 + rng.below(9), 2 + rng.below(7));
            let af = paired(layered(&mut rng, k, size, inner, cross));
            let query = rng.below(k * size);
            for assumptions in [vec![], vec![query]] {
                let expected = Solver::new(&af, Semantics::Stable, false).solve(&assumptions);
                let first = [Order::Topological, Order::Activity][rng.below(2)];
                let (answer, order) = portfolio(&af, &assumptions, 1 + rng.below(3), first, false, "test");
                won[(order == Order::Activity) as usize] += 1;
                second_answered += (order != first) as usize;
                assert_eq!(answer.is_some(), expected.is_some(),
                    "round {round}, {assumptions:?}: {answer:?} vs {expected:?}\n{af}");
                if let Some(extension) = &answer {
                    assert!(assumptions.iter().all(|a| extension.contains(a)) && af.is_stable(extension),
                        "round {round}, {assumptions:?}: {extension:?}\n{af}");
                    answers[0] += 1;
                } else {
                    answers[1] += 1;
                }
            }
        }
        assert!(won[0] > 200 && won[1] > 200, "one search hardly ever answers: {won:?}");
        assert!(second_answered > 40, "the second search rarely answers ({second_answered})");
        assert!(answers[0] > 200 && answers[1] > 100, "answers too one-sided: {answers:?}");
    }
}
