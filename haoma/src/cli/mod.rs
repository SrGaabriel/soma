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
    style::{self, ColorMode, Verbosity},
};

#[derive(Parser, Debug)]
#[command(name = "haoma", about = "Build tool for the Soma language", long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,

    #[arg(short, long, global = true, conflicts_with = "verbose")]
    pub quiet: bool,

    #[arg(short, long, global = true)]
    pub verbose: bool,

    #[arg(long, global = true, value_enum, default_value_t = ColorMode::Auto)]
    pub color: ColorMode,

    #[arg(long, global = true, help = "Path to log file")]
    pub log_file: Option<PathBuf>,
}

#[derive(clap::Subcommand, Debug)]
pub enum Commands {
    Build {
        #[arg(short, long, default_value = ".")]
        path: PathBuf,
        #[arg(long)]
        emit_llvm: bool,
        #[arg(long, default_value = "dev")]
        profile: String,
        #[arg(long, conflicts_with = "profile")]
        debug: bool,
        #[arg(long, conflicts_with = "profile")]
        release: bool,
        #[arg(long)]
        target: Option<String>,
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
        #[arg(long, default_value = "dev")]
        profile: String,
        #[arg(long, conflicts_with = "profile")]
        debug: bool,
        #[arg(long, conflicts_with = "profile")]
        release: bool,
        #[arg(long)]
        target: Option<String>,
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

pub fn resolve_profile(profile: &str, debug: bool, release: bool) -> &str {
    if debug {
        "debug"
    } else if release {
        "release"
    } else {
        profile
    }
}

pub fn parse() -> Cli {
    Cli::parse()
}

pub fn init_style(cli: &Cli) {
    let verbosity = if cli.quiet {
        Verbosity::Quiet
    } else if cli.verbose {
        Verbosity::Verbose
    } else {
        Verbosity::Normal
    };
    style::init(cli.color, verbosity);
}

pub fn execute(command: &Commands) {
    match command {
        Commands::Build {
            path,
            emit_llvm,
            profile,
            debug,
            release,
            target,
        } => {
            unsafe {
                if *emit_llvm {
                    std::env::set_var("SOMA_EMIT_LLVM", "1");
                }
                if style::is_verbose() {
                    std::env::set_var("SOMA_VERBOSE_LOGGING", "1");
                }
                std::env::set_var("SOMA_PROFILE", resolve_profile(profile, *debug, *release));
                if let Some(t) = target {
                    std::env::set_var("SOMA_TARGET", t);
                }
            }
            build::execute(path, resolve_profile(profile, *debug, *release));
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
            profile,
            debug,
            release,
            target,
            args,
        } => {
            unsafe {
                if *emit_llvm {
                    std::env::set_var("SOMA_EMIT_LLVM", "1");
                }
                std::env::set_var("SOMA_PROFILE", resolve_profile(profile, *debug, *release));
                if let Some(t) = target {
                    std::env::set_var("SOMA_TARGET", t);
                }
            }
            run::execute(path, args, resolve_profile(profile, *debug, *release));
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
        output_err(format!(
            "manifest file `{}` not found in `{}`",
            MANIFEST_NAME,
            path.display()
        ));
        std::process::exit(1);
    }
    output_debug(format!(
        "Found manifest file at '{}'",
        manifest_path.display()
    ));

    let content = match std::fs::read_to_string(&manifest_path) {
        Ok(c) => c,
        Err(e) => {
            output_err(format!("failed to read manifest file: {e}"));
            std::process::exit(1);
        }
    };

    match Manifest::parse(&content, MANIFEST_NAME) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("{:?}", miette::Report::new(e).with_source_code(content));
            output_err("failed to parse manifest file");
            std::process::exit(1);
        }
    }
}
