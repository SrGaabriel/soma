mod build;
mod create;
mod run;

use clap::Parser;
use std::path::{Path, PathBuf};

use crate::{
    config::manifest::{MANIFEST_NAME, Manifest},
    logging::{output_debug, output_err},
};

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
    Build {
        #[arg(short, long, default_value = ".")]
        path: PathBuf,
    },
    Create {
        #[arg(value_name = "path", default_value = ".")]
        path: PathBuf,
    },
    Run {
        #[arg(short, long, default_value = ".")]
        path: PathBuf,
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
}

pub fn parse() -> Cli {
    Cli::parse()
}

pub fn execute(command: &Commands) {
    match &command {
        Commands::Build { path } => {
            build::execute(path);
        }
        Commands::Create { path } => {
            create::execute(path);
        }
        Commands::Run { path, args } => {
            run::execute(path, args);
        }
    }
}

pub fn parse_manifest(path: &Path) -> Manifest {
    let manifest = path.join(MANIFEST_NAME);
    if !manifest.exists() {
        output_err(&format!(
            "Manifest file '{}' not found in path '{}'",
            MANIFEST_NAME,
            path.display()
        ));
        std::process::exit(1);
    }
    output_debug(&format!("Found manifest file at '{}'", manifest.display()));

    let parsing_result = std::fs::read_to_string(&manifest).and_then(|content| {
        toml::from_str::<Manifest>(&content)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    });
    if let Err(e) = parsing_result {
        output_err(&format!("Failed to parse manifest file: {}", e));
        std::process::exit(1);
    }
    parsing_result.unwrap()
}
