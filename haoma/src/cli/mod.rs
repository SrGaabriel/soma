mod create;
mod run;

use clap::Parser;
use colored::{Color, Colorize};
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "builder")]
#[command(about = "A simple custom build tool", long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(clap::Subcommand)]
pub enum Commands {
    Run {
        #[arg(short, long, default_value = ".")]
        path: PathBuf,
    },
    Create {
        #[arg(short, long)]
        path: PathBuf,
    },
}

pub fn parse_and_execute() {
    let cli = Cli::parse();
    match &cli.command {
        Commands::Run { path } => {
            run::execute(path);
        }
        Commands::Create { path } => {
            create::execute(path);
        }
    }
}

pub fn output_err(text: &str) {
    output_pretty("error", "⛔", Color::Red, text);
}

#[allow(dead_code)]
pub fn output_warning(text: &str) {
    output_pretty("warn", "⚠️", Color::Yellow, text);
}

pub fn output_debug(text: &str) {
    output_pretty("debug", "🐛", Color::Blue, text);
}

pub fn output_ok(text: &str) {
    output_pretty("success", "✅", Color::Green, text);
}

pub fn output_pretty(prefix: &str, emoji: &str, color: Color, text: &str) {
    println!(
        "{} {} {}",
        format!("[{prefix}]").color(color).bold(),
        emoji,
        text
    );
}
