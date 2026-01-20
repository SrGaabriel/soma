mod build;
mod check;
mod clean;
mod create;
mod metadata;
mod run;
mod somac;

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
        /// Keep the generated LLVM IR file (.ll) after compilation
        #[arg(long)]
        emit_llvm: bool,
    },
    Check {
        #[arg(short, long, default_value = ".")]
        path: PathBuf,
    },
    Create {
        #[arg(value_name = "path", default_value = ".")]
        path: PathBuf,
    },
    Clean {
        #[arg(short, long, default_value = ".")]
        path: PathBuf,
    },
    Run {
        #[arg(short, long, default_value = ".")]
        path: PathBuf,
        #[arg(long)]
        emit_llvm: bool,
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    Metadata {
        #[arg(short, long, default_value = ".")]
        path: PathBuf,
        #[arg(short, long)]
        full: bool,
    },
}

pub fn parse() -> Cli {
    Cli::parse()
}

pub fn execute(command: &Commands) {
    match &command {
        Commands::Build { path, emit_llvm } => {
            if *emit_llvm {
                unsafe {
                    std::env::set_var("SOMA_EMIT_LLVM", "1");
                }
            }
            build::execute(path);
        }
        Commands::Check { path } => {
            check::execute(path);
        }
        Commands::Create { path } => {
            create::execute(path);
        }
        Commands::Run {
            path,
            emit_llvm,
            args,
        } => {
            if *emit_llvm {
                unsafe {
                    std::env::set_var("SOMA_EMIT_LLVM", "1");
                }
            }
            run::execute(path, args);
        }
        Commands::Clean { path } => {
            clean::execute(path);
        }
        Commands::Metadata { path, full } => {
            metadata::execute(path, *full);
        }
    }
}

pub fn parse_manifest(path: &Path) -> Manifest {
    let manifest_path = path.join(MANIFEST_NAME);
    if !manifest_path.exists() {
        output_err(&format!(
            "Manifest file '{}' not found in path '{}'",
            MANIFEST_NAME,
            path.display()
        ));
        std::process::exit(1);
    }
    output_debug(&format!(
        "Found manifest file at '{}'",
        manifest_path.display()
    ));

    let content = match std::fs::read_to_string(&manifest_path) {
        Ok(c) => c,
        Err(e) => {
            output_err(&format!("Failed to read manifest file: {}", e));
            std::process::exit(1);
        }
    };

    match Manifest::parse(&content, MANIFEST_NAME) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("{:?}", miette::Report::new(e).with_source_code(content));
            output_err("Failed to parse manifest file");
            std::process::exit(1);
        }
    }
}
