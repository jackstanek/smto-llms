use clap::Parser;
use log::{debug, info};

#[macro_use]
mod macros;
mod concrete_theories;
mod solvers;
mod theories;

#[derive(Parser, Debug)]
#[command(version)]
pub struct Args {}

fn main() {
    let args = Args::parse();
    debug!("{:?}", &args);
}
