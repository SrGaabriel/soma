use std::path::Path;

use crate::{
    build::build_project,
    cli::parse_manifest,
    logging::{output_debug, output_err, output_ok},
};

pub fn execute(path: &Path) {
    let manifest = parse_manifest(path);
    output_debug("Successfully read manifest file");
    match build_project(path, &manifest) {
        Ok(build) => {
            output_ok(&format!("Build successful! Stats: {:?}", build));
        }
        Err(e) => {
            output_err(&format!("Build failed: {}", e));
        }
    }
}
