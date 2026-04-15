#![warn(clippy::pedantic)]
#![allow(clippy::too_many_lines)]

mod cli;
mod core;
mod tui;

use cli::{Cli, CommandRunner, Commands, SelfCommands};

fn main() {
    if let Err(e) = run() {
        eprintln!("Error: {e}");
        std::process::exit(1);
    }
}

fn run() -> core::Result<()> {
    let cli = Cli::parse_args();

    match cli.command {
        Commands::Install { version } => {
            let runner = CommandRunner::new()?;
            runner.install(&version)?;
        }

        Commands::Dev { path, copy, only } => {
            let runner = CommandRunner::new()?;
            runner.dev(path, copy, only.as_ref())?;
        }

        Commands::Use { version } => {
            let runner = CommandRunner::new()?;
            runner.use_version(&version)?;
        }

        Commands::List => {
            let runner = CommandRunner::new()?;
            runner.list()?;
        }

        Commands::Current => {
            let runner = CommandRunner::new()?;
            runner.current()?;
        }

        Commands::Uninstall { version } => {
            let runner = CommandRunner::new()?;
            runner.uninstall(&version)?;
        }

        Commands::Setup { shell } => {
            let runner = CommandRunner::new()?;
            runner.setup(shell)?;
        }

        Commands::Tui => {
            tui::run_tui()?;
        }

        Commands::SelfCmd { command } => match command {
            SelfCommands::Uninstall { yes } => {
                cli::self_uninstall(yes)?;
            }
        },
    }

    Ok(())
}
