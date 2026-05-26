use std::{path::Path, process::Command};

use super::build::print_build_summary;
use crate::{
    build::build_project,
    cli::parse_manifest,
    config::manifest::ManifestModuleType,
    logging::{output_debug, output_err},
    style::{self, Tone},
};

pub fn execute(path: &Path, args: &[String], profile: &str) {
    let manifest = parse_manifest(path);
    output_debug("Successfully read manifest file");
    if manifest.module_type != ManifestModuleType::Binary {
        output_err("the specified project is not a binary module");
        std::process::exit(1);
    }

    let build = match build_project(path, &manifest) {
        Ok(b) => b,
        Err(e) => {
            output_err(format!("build failed: {e}"));
            std::process::exit(1);
        }
    };
    print_build_summary(&build, profile);

    let Some(binary) = build.final_binary_path else {
        output_err("build produced no binary");
        std::process::exit(1);
    };

    style::status(Tone::Progress, "running", format!("· {}", binary.display()));
    let exit_status = Command::new(&binary)
        .args(args)
        .status()
        .expect("Failed to execute process");

    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(1));
    }
}
