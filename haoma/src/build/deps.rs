use std::path::{Path, PathBuf};

use crate::{build::metadata::BuildTarball, config::manifest::{ManifestDependencies, ManifestDependencyValue}, logging::output_err};

#[derive(Debug)]
#[allow(dead_code)]
pub enum DependencyAction {
    Include {
        name: String,
        tarball: PathBuf,
    },
    Compile { path: PathBuf },
    Download { url: String, checksum: String },
    NotFound
}

pub fn extract_deps(name: String, manifest_deps: &ManifestDependencies) -> Vec<DependencyAction> {
    let mut actions = Vec::new();
    for (dep_name, dep) in &manifest_deps.dependencies {
        match dep {
            ManifestDependencyValue::Custom { path, version } => {
                let parsed_path = Path::new(&path);
                if !parsed_path.exists() {
                    output_err(&format!("Could not find module '{}' at path '{}' (required by {})", dep_name, path, name));
                    std::process::exit(1);
                }
                let build_tarball_path = parsed_path.join("build").join(format!("{}.toria", dep_name));
                let build_tarball = BuildTarball::open(&build_tarball_path);
                if let Err(e) = build_tarball {
                    output_err(&format!("Failed to read build metadata for module '{}' at path '{}' (required by {}): {}", dep_name, path, name, e));
                    std::process::exit(1);
                }
                let build_tarball = build_tarball.unwrap();
                let build_metadata = build_tarball.metadata.minimal;

                if build_metadata.module_name != *dep_name {
                    output_err(&format!("Module name mismatch for module '{}' at path '{}' (required by {}). Expected '{}', found '{}'", dep_name, path, name, dep_name, build_metadata.module_name));
                    std::process::exit(1);
                }
                if let Some(version) = version && build_metadata.version != *version {
                    output_err(&format!("Module version mismatch for module '{}' at path '{}' (required by {}). Expected '{}', found '{}'", dep_name, path, name, version, build_metadata.version));
                    std::process::exit(1);
                }
                actions.push(DependencyAction::Include {
                    name: dep_name.clone(),
                    tarball: build_tarball_path,
                });
            }
            _ => todo!()
        }
    }
    actions
}
