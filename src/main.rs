use clap::{Parser, ValueEnum};
use std::fs::File;
use execution_time::ExecutionTime;

mod af;
mod algorithms;
mod io;

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
}

fn main() -> std::io::Result<()> {
    let params = Params::parse();
    let input_af = File::open(params.input_file)?;

    // Start the timer
    let timer = ExecutionTime::start();
    let af = read_af(input_af);
    println!("Elapsed time: {}", timer.get_elapsed_time());

    match params.problem {
        Problem::DcCo => {
            let arg = params.argument.unwrap();
            if arg == 0 {
                panic!("Argument id must be >= 1");
            }
            match dc_co(&af, arg - 1) {
                Some(extension) => {
                    let mut extension: Vec<usize> = extension.into_iter().map(|a| a + 1).collect();
                    extension.sort_unstable();
                    println!("YES");
                    println!("{:?}", extension);
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
    }

    Ok(())
}
