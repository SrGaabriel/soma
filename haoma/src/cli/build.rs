use std::path::Path;

use crate::{
    build::{BuildOutput, build_src},
    cli::parse_manifest,
    config::manifest::ManifestModuleType,
    logging::{output_debug, output_ok},
};

pub fn execute(path: &Path) {
    let manifest = parse_manifest(path);
    output_debug("Successfully read manifest file");
    let output_type = match manifest.module_type {
        ManifestModuleType::Library => BuildOutput::Tarball,
        ManifestModuleType::Binary => BuildOutput::Object,
    };
    let exec_path = build_src(path, &manifest, output_type);
    output_ok(&format!(
        "Build successful! Executable located at: {}",
        exec_path.display()
    ));
}
