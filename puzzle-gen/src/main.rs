use anyhow::Context;
use clap::Parser;
use log::{Level, debug, info};

#[macro_use]
mod macros;
mod concrete_theories;
mod solvers;
mod theories;

#[derive(Parser, Debug)]
#[command(version)]
pub struct Args {
    /// Log level
    #[arg(long, default_value_t = Level::Info)]
    log_level: Level,
}

/// Set up the logger.
///
/// Log all messages above the specified log level.
fn logger_setup(level: &Level) -> anyhow::Result<()> {
    env_logger::builder()
        .filter_level(level.to_level_filter())
        .try_init()
        .context("couldn't initialize logger")
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    logger_setup(&args.log_level)?;
    info!("puzzle-gen started");

    info!("exiting");
    Ok(())
}
