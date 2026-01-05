mod commands;

use clap::{Parser, Subcommand};
use std::path::PathBuf;

pub use commands::*;

#[derive(Parser)]
#[command(name = "svm")]
#[command(author, version, about = "Soma Version Manager", long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand)]
pub enum Commands {
    Install {
        version: String,
    },
    Dev {
        #[arg(long, short)]
        path: Option<PathBuf>,
        #[arg(long)]
        copy: bool,
        #[arg(long, short, value_delimiter = ',')]
        only: Option<Vec<String>>,
    },
    Use {
        version: String,
    },
    List,
    Current,
    Uninstall {
        version: String,
    },
    Setup {
        #[arg(long)]
        shell: Option<String>,
    },
    Tui,
    #[command(name = "self")]
    SelfCmd {
        #[command(subcommand)]
        command: SelfCommands,
    },
}

#[derive(Subcommand)]
pub enum SelfCommands {
    Uninstall {
        #[arg(long, short = 'y')]
        yes: bool,
    },
}

impl Cli {
    pub fn parse_args() -> Self {
        Self::parse()
    }
}
