use std::collections::HashMap;
use std::path::Path;

use serde::Serialize;

use crate::build::consts::SRC_FOLDER_NAME;
use crate::build::resolve::DependencyResolver;
use crate::cli::parse_manifest;
use crate::cli::somac;
use crate::logging::output_err;

#[derive(Debug, Clone, Serialize)]
pub struct ModuleInfo {
    pub name: String,
    pub path: String,
    pub package: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct PackageInfo {
    pub name: String,
    pub root: String,
    pub version: String,
    pub is_root: bool,
    pub dependencies: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ProjectMetadata {
    pub success: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    pub root_package: String,
    pub packages: Vec<PackageInfo>,
    pub modules: Vec<ModuleInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_metadata: Option<HashMap<String, String>>,
}

pub fn execute(path: &Path, full: bool) {
    let manifest = parse_manifest(path);
    let root_name = manifest.name.clone();

    let mut resolver = DependencyResolver::new(path.to_path_buf());
    let graph = match resolver.resolve(&manifest) {
        Ok(g) => g,
        Err(e) => {
            output_err(&format!("Failed to resolve dependencies: {e}"));
            let output = ProjectMetadata {
                success: false,
                error: Some(format!("{e}")),
                root_package: root_name,
                packages: vec![],
                modules: vec![],
                type_metadata: None,
            };
            println!("{}", serde_json::to_string(&output).unwrap());
            std::process::exit(1);
        }
    };

    let mut packages = Vec::new();
    let mut all_modules = Vec::new();

    for (name, node) in graph.nodes() {
        let is_root = name == &root_name;
        let root_path = node
            .path
            .canonicalize()
            .unwrap_or_else(|_| node.path.clone());

        packages.push(PackageInfo {
            name: name.clone(),
            root: root_path.display().to_string(),
            version: node.manifest.version.clone(),
            is_root,
            dependencies: node.dependencies.clone(),
        });

        let src_dir = node.path.join(SRC_FOLDER_NAME);
        if src_dir.exists()
            && let Ok(modules) = scan_modules(name, &src_dir)
        {
            all_modules.extend(modules);
        }
    }

    packages.sort_by(|a, b| a.name.cmp(&b.name));
    all_modules.sort_by(|a, b| a.name.cmp(&b.name));

    let type_metadata = if full {
        match somac::generate_all_metadata(&graph) {
            Ok(metadata_paths) => Some(
                metadata_paths
                    .into_iter()
                    .map(|(k, v)| (k, v.display().to_string()))
                    .collect(),
            ),
            Err(e) => {
                let output = ProjectMetadata {
                    success: false,
                    error: Some(format!("Failed to generate type metadata: {e}")),
                    root_package: root_name,
                    packages,
                    modules: all_modules,
                    type_metadata: None,
                };
                println!("{}", serde_json::to_string(&output).unwrap());
                std::process::exit(1);
            }
        }
    } else {
        None
    };

    let output = ProjectMetadata {
        success: true,
        error: None,
        root_package: root_name,
        packages,
        modules: all_modules,
        type_metadata,
    };

    println!("{}", serde_json::to_string(&output).unwrap());
}

fn scan_modules(package_name: &str, src_dir: &Path) -> Result<Vec<ModuleInfo>, std::io::Error> {
    let mut modules = Vec::new();
    scan_modules_recursive(package_name, src_dir, "", &mut modules)?;
    Ok(modules)
}

fn scan_modules_recursive(
    package_name: &str,
    dir: &Path,
    prefix: &str,
    modules: &mut Vec<ModuleInfo>,
) -> Result<(), std::io::Error> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let file_name = entry.file_name();
        let file_name_str = file_name.to_string_lossy();

        if path.is_dir() {
            let new_prefix = if prefix.is_empty() {
                file_name_str.to_string()
            } else {
                format!("{prefix}/{file_name_str}")
            };
            scan_modules_recursive(package_name, &path, &new_prefix, modules)?;
        } else if path.extension().is_some_and(|e| e == "soma") {
            let module_suffix = if prefix.is_empty() {
                file_name_str.trim_end_matches(".soma").to_string()
            } else {
                format!("{}/{}", prefix, file_name_str.trim_end_matches(".soma"))
            };

            let module_name = format!("{package_name}/{module_suffix}");
            let abs_path = path.canonicalize().unwrap_or_else(|_| path.clone());

            modules.push(ModuleInfo {
                name: module_name,
                path: abs_path.display().to_string(),
                package: package_name.to_string(),
            });
        }
    }
    Ok(())
}
