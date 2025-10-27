use colored::Color;
use std::path::Path;

use crate::{
    config::manifest::{MANIFEST_NAME, Manifest, ManifestDependencies, ManifestModuleType},
    logging::{output_debug, output_err, pretty_print},
};

pub fn execute(path: &Path) {
    if path.exists() {
        output_err("The specified path already exists.");
        std::process::exit(1);
    }
    if let Err(e) = std::fs::create_dir_all(path) {
        output_err(&format!(
            "Failed to create directory at '{}': {}",
            path.display(),
            e
        ));
        std::process::exit(1);
    }
    output_debug(&format!(
        "Successfully created directory at '{}'",
        path.display()
    ));
    let project_name = path
        .file_name()
        .expect("Failed to get project name from path")
        .to_str();
    if project_name.is_none() {
        output_err("Project name contains invalid UTF-8 characters.");
        std::process::exit(1);
    }

    let manifest = Manifest {
        name: project_name.unwrap().to_owned(),
        version: "0.1.0".to_string(),
        module_type: ManifestModuleType::Binary,
        authors: None,
        dependencies: ManifestDependencies::new(),
    };
    let manifest_content =
        toml::to_string(&manifest).expect("Failed to serialize manifest to TOML");

    let manifest_path = path.join(MANIFEST_NAME);
    if let Err(e) = std::fs::write(&manifest_path, manifest_content) {
        output_err(&format!(
            "Failed to write manifest file at '{}': {}",
            manifest_path.display(),
            e
        ));
        std::process::exit(1);
    }

    output_debug(&format!(
        "Successfully created manifest file at '{}'",
        manifest_path.display()
    ));

    let main = path.join("src").join("main.soma");

    if let Err(e) = std::fs::create_dir_all(main.parent().unwrap()) {
        output_err(&format!(
            "Failed to create source directory at '{}': {}",
            main.parent().unwrap().display(),
            e
        ));
        std::process::exit(1);
    }
    if let Err(e) = std::fs::write(&main, "def main :: IO ()\n    println \"Hello, World!\"\n") {
        output_err(&format!(
            "Failed to write main source file at '{}': {}",
            main.display(),
            e
        ));
        std::process::exit(1);
    }
    output_debug(&format!(
        "Successfully created main source file at '{}'",
        main.display()
    ));

    tracing::info!("The Soma project has been initialized successfully.");
    pretty_print(
        "welcome",
        "🚀",
        Color::Magenta,
        &format!(
            "Successfully initialized new Soma project at '{}'!",
            path.display()
        ),
    );
}
