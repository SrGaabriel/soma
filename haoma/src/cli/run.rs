use std::{path::Path, process::Command};

use crate::{
    build::{BuildOutput, build_src},
    cli::parse_manifest,
    logging::{output_debug, output_err, output_ok},
};

pub fn execute(path: &Path, args: &Vec<String>) {
    let manifest = parse_manifest(path);
    output_debug("Successfully read manifest file");
    let executable = build_src(path, &manifest, BuildOutput::Object);
    output_ok("Executable built successfully. Now executing...");

    let exit_status = Command::new(executable)
        .args(args)
        .status()
        .expect("Failed to execute process");
    println!();
    if !exit_status.success() {
        let exit_code = exit_status.code().map(|x| x.to_string());
        output_err(&format!(
            "Process exited with status: {}",
            exit_code.unwrap_or("?".to_string())
        ));
        std::process::exit(exit_status.code().unwrap_or(1));
    } else {
        output_ok("Process executed successfully");
    }
}
