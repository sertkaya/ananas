use clap::{Parser, ValueEnum};
use std::fs::File;
use execution_time::ExecutionTime;

mod af;
mod algorithms;
mod io;

use std::collections::HashSet;
use crate::algorithms::complete::dc_co;
use crate::io::af_parser::read_af;

#[derive(Clone, Copy, ValueEnum)]
enum Problem {
    #[value(name = "DC-CO")]
    DcCo,
    #[value(name = "DC-ST")]
    DcSt,
    #[value(name = "SE-PR")]
    SePr,
    /// Verify that a given extension is complete
    #[value(name = "VE-CO")]
    VeCo,
    /// Verify that a given extension is stable
    #[value(name = "VE-ST")]
    VeSt,
}

#[derive(Parser)]
struct Params {
    /// Path to the input argumentation framework
    #[arg(short = 'i', long = "input", value_name = "FILE")]
    input_file: std::path::PathBuf,

    /// The reasoning problem to solve
    #[arg(short = 'p', long = "problem", value_enum)]
    problem: Problem,

    /// The argument to decide credulous acceptance for (1-indexed, as in
    /// the input file); required for DC-CO and DC-ST
    #[arg(
        short = 'a',
        long = "argument",
        required_if_eq("problem", "DC-CO"),
        required_if_eq("problem", "DC-ST")
    )]
    argument: Option<usize>,

    /// Path to a file containing the extension to verify, in ICCMA solver
    /// output format: a first line "YES", then a second line "w " followed
    /// by a blank-separated list of argument ids (1-indexed, as in the
    /// input file); required for VE-CO and VE-ST
    #[arg(
        short = 'e',
        long = "extension",
        value_name = "FILE",
        required_if_eq("problem", "VE-CO"),
        required_if_eq("problem", "VE-ST")
    )]
    extension: Option<std::path::PathBuf>,

    /// Print search-tree size diagnostics (nodes visited, pseudo_complete
    /// calls) to stderr as the solver runs
    #[arg(short = 'v', long = "verbose")]
    verbose: bool,
}

fn main() -> std::io::Result<()> {
    let params = Params::parse();
    let input_af = File::open(params.input_file)?;

    // Start the timer
    let timer = ExecutionTime::start();
    let af = read_af(input_af);
    if params.verbose {
        println!("Parsing time: {}", timer.get_elapsed_time());
    }

    match params.problem {
        Problem::DcCo => {
            let arg = params.argument.unwrap();
            if arg == 0 {
                panic!("Argument id must be >= 1");
            }
            let solve_timer = ExecutionTime::start();
            let result = dc_co(&af, arg - 1, params.verbose);
            if params.verbose {
                println!("Solving time: {}", solve_timer.get_elapsed_time());
            }
            match result {
                Some(extension) => {
                    let mut extension: Vec<usize> = extension.into_iter().map(|a| a + 1).collect();
                    extension.sort_unstable();
                    let witness = extension
                        .iter()
                        .map(|a| a.to_string())
                        .collect::<Vec<_>>()
                        .join(" ");
                    println!("YES");
                    println!("w {witness}");
                }
                None => println!("NO"),
            }
        }
        Problem::DcSt => {
            unimplemented!("DC-ST is not yet implemented");
        }
        Problem::SePr => {
            unimplemented!("SE-PR is not yet implemented");
        }
        Problem::VeCo | Problem::VeSt => {
            let extension_file = params.extension.unwrap();
            let content = std::fs::read_to_string(extension_file)?;
            let mut lines = content.lines();
            let first = lines
                .next()
                .expect("Extension file must have a first line \"YES\"");
            if first.trim() != "YES" {
                panic!("Extension file's first line must be \"YES\"");
            }
            let second = lines
                .next()
                .expect("Extension file must have a second line starting with \"w\"");
            let mut tokens = second.split_whitespace();
            if tokens.next() != Some("w") {
                panic!("Extension file's second line must start with \"w\"");
            }
            let mut set = HashSet::new();
            for token in tokens {
                let arg: usize = token
                    .parse()
                    .expect("Extension file's second line must contain whitespace-separated argument ids after \"w\"");
                if arg == 0 || arg > af.argument_count() {
                    panic!("Argument id must be between 1 and {}", af.argument_count());
                }
                set.insert(arg - 1);
            }
            let result = match params.problem {
                Problem::VeCo => af.is_complete(&set),
                Problem::VeSt => af.is_stable(&set),
                _ => unreachable!(),
            };
            println!("{}", if result { "YES" } else { "NO" });
        }
    }

    Ok(())
}
