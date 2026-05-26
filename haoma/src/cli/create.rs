use std::path::Path;

use crate::{
    build::consts::SRC_FOLDER_NAME,
    config::manifest::{MANIFEST_NAME, Manifest, ManifestDependencies, ManifestModuleType},
    logging::{output_debug, output_err},
    style::{self, Tone},
};

pub fn execute(path: &Path) {
    if path.exists() {
        output_err(format!("`{}` already exists", path.display()));
        std::process::exit(1);
    }
    if let Err(e) = std::fs::create_dir_all(path) {
        output_err(format!("failed to create `{}`: {e}", path.display()));
        std::process::exit(1);
    }
    output_debug(format!("created directory `{}`", path.display()));

    let Some(project_name) = path.file_name().and_then(|n| n.to_str()) else {
        output_err("project name contains invalid UTF-8 characters");
        std::process::exit(1);
    };

    let manifest = Manifest {
        name: project_name.to_owned(),
        version: "0.1.0".to_string(),
        module_type: ManifestModuleType::Binary,
        authors: None,
        dependencies: ManifestDependencies::new(),
    };
    let manifest_content = manifest.to_kdl();

    let manifest_path = path.join(MANIFEST_NAME);
    if let Err(e) = std::fs::write(&manifest_path, manifest_content) {
        output_err(format!(
            "failed to write manifest at `{}`: {e}",
            manifest_path.display()
        ));
        std::process::exit(1);
    }
    output_debug(format!("wrote manifest at `{}`", manifest_path.display()));

    let main = path.join(SRC_FOLDER_NAME).join("main.soma");
    if let Err(e) = std::fs::create_dir_all(main.parent().unwrap()) {
        output_err(format!(
            "failed to create source directory `{}`: {e}",
            main.parent().unwrap().display()
        ));
        std::process::exit(1);
    }
    if let Err(e) = std::fs::write(&main, "def main : IO () = println \"Hello, World!\"\n") {
        output_err(format!("failed to write `{}`: {e}", main.display()));
        std::process::exit(1);
    }
    output_debug(format!("wrote source file `{}`", main.display()));

    tracing::info!("Initialized Soma project `{project_name}`");
    style::status(
        Tone::Success,
        "created",
        format!("· {project_name} (binary)"),
    );
}
