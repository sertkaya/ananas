// use crate::af::AF;
use clap::Parser;
use std::fs::File;
use execution_time::ExecutionTime;

use crate::af_parser::read_af;

pub mod af;
pub mod af_parser;

#[derive(Parser)]
struct Params {
    /// Path to the input argumentation framework
    #[arg(short = 'i', long = "input", value_name = "FILE" )]
    input_file: std::path::PathBuf,
}

fn main()  -> std::io::Result<()> {
    let params = Params::parse();
    let input_af = File::open(params.input_file)?;

    // Start the timer
    let timer = ExecutionTime::start();
    let af = read_af(input_af);
    println!("Elapsed time: {}", timer.get_elapsed_time());

    println!("{}", af.get_arg_count());

    Ok(())
}
