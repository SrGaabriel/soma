use std::path::Path;

use crate::{
    build::build_src,
    cli::parse_manifest,
    logging::{output_debug, output_ok},
};

pub fn execute(path: &Path) {
    let manifest = parse_manifest(path);
    output_debug("Successfully read manifest file");
    let exec_path = build_src(path, &manifest);
    output_ok(&format!(
        "Build successful! Executable located at: {}",
        exec_path.display()
    ));
}
