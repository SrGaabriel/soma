use std::path::Path;

use crate::{
    cli::{output_debug, output_err, output_ok},
    config::manifest::{MANIFEST_NAME, Manifest},
};

pub fn execute(path: &Path) {
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

    output_debug("Successfully read manifest file");
    let manifest = parsing_result.unwrap();

    output_ok(&format!(
        "Running project '{}' version '{}'",
        manifest.name, manifest.version
    ));
}
