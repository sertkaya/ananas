use clap::Parser;
use std::fs::File;
use execution_time::ExecutionTime;

mod af;
mod algorithms;
mod io;

use crate::io::af_parser::read_af;

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

    println!("{}", af.argument_count());

    Ok(())
}
