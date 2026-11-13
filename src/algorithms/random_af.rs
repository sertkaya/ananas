//! Small random argumentation frameworks for property tests, from a seeded
//! xorshift generator so that every run sees the same frameworks and a
//! failure can be reproduced from the seed it reports.

use crate::af::AF;

/// A xorshift64 pseudo-random generator
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        // xorshift gets stuck at 0, and nearby seeds start out correlated,
        // so scramble the seed first
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// A uniformly random number in `0..n`
    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// A framework with `n` arguments in which each of the `n * n` possible
/// attacks, self-attacks included, is present with probability
/// `percent / 100`
pub fn random_af(rng: &mut Rng, n: usize, percent: usize) -> AF {
    let mut af = AF::new(n);
    for a in 0..n {
        for b in 0..n {
            if rng.below(100) < percent {
                af.add_attack(a, b);
            }
        }
    }
    af
}
