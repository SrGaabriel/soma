mod create;
mod run;

use clap::Parser;
use colored::{Color, Colorize};
use std::path::PathBuf;
use tracing::{debug, error, info, warn};

#[derive(Parser, Debug)]
#[command(name = "builder")]
#[command(about = "A simple custom build tool", long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
    #[arg(short, long, global = true, help = "Path to log file")]
    pub log_file: Option<PathBuf>,
}

#[derive(clap::Subcommand, Debug)]
pub enum Commands {
    Run {
        #[arg(short, long, default_value = ".")]
        path: PathBuf,
    },
    Create {
        #[arg(value_name = "path", default_value = ".")]
        path: PathBuf,
    },
}

pub fn parse() -> Cli {
    Cli::parse()
}

pub fn execute(command: &Commands) {
    match &command {
        Commands::Run { path } => {
            run::execute(path);
        }
        Commands::Create { path } => {
            create::execute(path);
        }
    }
}

pub fn output_err(text: &str) {
    pretty_print("error", "⛔", colored::Color::Red, text);
    error!("{}", text);
}

#[allow(dead_code)]
pub fn output_warning(text: &str) {
    pretty_print("warn", "⚠️", colored::Color::Yellow, text);
    warn!("{}", text);
}

pub fn output_debug(text: &str) {
    debug!("{}", text);
}

pub fn output_ok(text: &str) {
    pretty_print("success", "✅", colored::Color::Green, text);
    info!("{}", text);
}

fn pretty_print(prefix: &str, emoji: &str, color: Color, text: &str) {
    println!(
        "{} {} {}",
        format!("[{prefix}]").color(color).bold(),
        emoji,
        text
    );
}
