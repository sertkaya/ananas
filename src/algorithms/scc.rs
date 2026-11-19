//! Strongly connected components, numbered in topological order of the
//! condensation, for deciding the arguments of source components first.

use crate::af::AF;

/// One frame of the depth-first search, standing in for a recursive call:
/// the argument, and how many of its victims have been looked at
struct Frame {
    arg: usize,
    next: usize,
}

/// Each argument's strongly connected component, by Tarjan's algorithm run
/// with an explicit stack, so that its depth does not depend on the
/// framework. Components are numbered in topological order: if `a` attacks
/// `b`, then `a`'s component number is at most `b`'s, and equal exactly
/// when they are in the same component. Sources therefore come first.
pub fn topological_components(af: &AF) -> Vec<usize> {
    let n = af.argument_count();
    let mut index = vec![usize::MAX; n];
    let mut lowlink = vec![0; n];
    let mut on_stack = vec![false; n];
    let mut stack = Vec::new();
    let mut component = vec![0; n];
    let mut next_index = 0;
    // Tarjan completes the components sinks first; numbered from n down,
    // and shifted to start at 0 at the end
    let mut next_component = n;
    let mut work: Vec<Frame> = Vec::new();

    for start in 0..n {
        if index[start] != usize::MAX {
            continue;
        }
        work.push(Frame { arg: start, next: 0 });
        index[start] = next_index;
        lowlink[start] = next_index;
        next_index += 1;
        stack.push(start);
        on_stack[start] = true;

        while let Some(frame) = work.last_mut() {
            let v = frame.arg;
            if let Some(&w) = af.victims(v).as_slice().get(frame.next) {
                frame.next += 1;
                if index[w] == usize::MAX {
                    index[w] = next_index;
                    lowlink[w] = next_index;
                    next_index += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    work.push(Frame { arg: w, next: 0 });
                } else if on_stack[w] {
                    lowlink[v] = lowlink[v].min(index[w]);
                }
                continue;
            }
            work.pop();
            if let Some(parent) = work.last() {
                lowlink[parent.arg] = lowlink[parent.arg].min(lowlink[v]);
            }
            if lowlink[v] == index[v] {
                next_component -= 1;
                loop {
                    let w = stack.pop().expect("v is on the stack");
                    on_stack[w] = false;
                    component[w] = next_component;
                    if w == v {
                        break;
                    }
                }
            }
        }
    }
    for c in &mut component {
        *c -= next_component;
    }
    component
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::random_af::{random_af, Rng};

    #[test]
    fn test_chain_is_all_singletons_in_order() {
        // 0 -> 1 -> 2 -> 3
        let mut af = AF::new(4);
        af.add_attack(0, 1);
        af.add_attack(1, 2);
        af.add_attack(2, 3);
        assert_eq!(topological_components(&af), vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_cycle_feeding_a_cycle() {
        // 2 <-> 3 attacks 0 <-> 1: the source cycle comes first
        let mut af = AF::new(4);
        af.add_attack(0, 1);
        af.add_attack(1, 0);
        af.add_attack(2, 3);
        af.add_attack(3, 2);
        af.add_attack(3, 0);
        assert_eq!(topological_components(&af), vec![1, 1, 0, 0]);
    }

    // On random frameworks, two arguments share a component exactly when
    // each reaches the other, and every attack goes from a component to
    // itself or a later one.
    #[test]
    fn test_components_match_reachability() {
        let mut rng = Rng::new(12);
        for _ in 0..300 {
            let n = 1 + rng.below(25);
            let percent = [3, 6, 10, 20][rng.below(4)];
            let af = random_af(&mut rng, n, percent);
            let component = topological_components(&af);
            // reach[a][b]: b is reachable from a, by attack paths of any length
            let mut reach = vec![vec![false; n]; n];
            for (a, row) in reach.iter_mut().enumerate() {
                row[a] = true;
                let mut stack = vec![a];
                while let Some(v) = stack.pop() {
                    for &w in af.victims(v) {
                        if !row[w] {
                            row[w] = true;
                            stack.push(w);
                        }
                    }
                }
            }
            for a in 0..n {
                for b in 0..n {
                    assert_eq!(component[a] == component[b], reach[a][b] && reach[b][a], "{a}, {b}\n{af}");
                    if af.attacks(a, b) {
                        assert!(component[a] <= component[b], "{a} -> {b}\n{af}");
                    }
                }
            }
            let count = component.iter().max().map_or(0, |&c| c + 1);
            assert!((0..count).all(|c| component.contains(&c)), "numbers not contiguous");
        }
    }
}
