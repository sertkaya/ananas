# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project overview

Ananas ("A New and Neat Argumentation Solver") is a Rust CLI tool for working with abstract
argumentation frameworks (AFs) as studied in formal argumentation theory. It parses AF instance
files and will grow into a solver for argumentation semantics (e.g. computing extensions).

## Commands

- Build: `cargo build`
- Run: `cargo run -- -i <path-to-af-file>` (e.g. `cargo run -- -i tests/jelia23-example.af`)
- Run all tests: `cargo test`
- Run a single test: `cargo test test_af` or `cargo test test_read_af`
- Tests are plain `#[cfg(test)] mod tests` blocks embedded in each source file (see `src/af.rs`,
  `src/io/af_parser.rs`), not a separate `tests/` integration suite — `tests/` only holds `.af`
  fixture data.

## Architecture

- `src/main.rs` — CLI entry point (`clap` derive). `-i` input file, `-p` problem (DC-CO, DC-ST,
  SE-ST, SE-PR, VE-CO, VE-ST), `-a` argument (1-indexed, for DC-*), `-e` extension file (for
  VE-*), `-v` verbose diagnostics on stderr.
- `src/af.rs` — `AF`: arguments are `usize`, attacks are stored twice as sorted `Vec<Vec<usize>>`
  adjacency lists (`attacks[a]` = arguments `a` attacks, `attacked_by[a]` = arguments attacking
  `a`). Sorted so that iteration order, and hence the search, is deterministic. Also the
  extension checks `is_complete`/`is_stable`.
- `src/io/af_parser.rs` — `read_af(File) -> AF`: first line `p af <n>`, then `attacker victim`
  pairs; `#` lines and blank lines skipped. **1-indexed in the file, 0-indexed internally.**
- `src/algorithms/` — the solver, a CDCL search over the closure operator of the KR'26 paper:
  - `lit.rs` — vocabulary: `Value`, `Lit` (`In`/`Out`/`Def`), `Reason`, `Assignment`, `Semantics`.
  - `node.rs` — `Node`: the one search state (assignment, trail, decision levels, the counters
    the closure rules use, the clause database). Backtracking undoes the trail; nothing is cloned.
  - `closure.rs` — the propagator: semi-/quasi-complete rules, completeness, single/no-defender,
    the stable rule (every `Out` is `Def`), `backtrack_to_level`, `pseudo_complete`.
  - `clauses.rs` — `ClauseDb`: learned clauses with two watched literals, `propagate_clauses`.
  - `learning.rs` — `Analyzer`: 1UIP conflict analysis (`Def` resolved into its source literal),
    recursive clause minimization.
  - `search.rs` — `Solver::new(af, semantics, verbose).solve(assumptions)`: the CDCL loop and
    decision heuristic, shared by all problems; learned clauses stay valid as assumptions grow.
  - `complete.rs` (`dc_co`), `stable.rs` (`dc_st`, `se_st`) — thin wrappers over `Solver`.
  - `stats.rs` — verbose diagnostics. `random_af.rs` — seeded random AFs for property tests.
- Tests are property tests against brute-force enumeration (`is_complete`/`is_stable`) on random
  small AFs, plus hand-built cases for specific rules; run `cargo test --release`.
