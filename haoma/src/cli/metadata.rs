use std::path::Path;

use serde::Serialize;

use crate::build::resolve::DependencyResolver;
use crate::cli::parse_manifest;
use crate::logging::output_err;

/// A resolved module in the project
#[derive(Debug, Clone, Serialize)]
pub struct ModuleInfo {
    /// Full module name (e.g., "myapp/utils/io")
    pub name: String,
    /// Absolute path to the .soma file
    pub path: String,
    /// Package this module belongs to
    pub package: String,
}

/// A resolved package (the current project or a dependency)
#[derive(Debug, Clone, Serialize)]
pub struct PackageInfo {
    /// Package name
    pub name: String,
    /// Absolute path to package root
    pub root: String,
    /// Package version
    pub version: String,
    /// Whether this is the root package or a dependency
    pub is_root: bool,
    /// Dependencies of this package
    pub dependencies: Vec<String>,
}

/// Full project metadata output
#[derive(Debug, Clone, Serialize)]
pub struct ProjectMetadata {
    /// Whether metadata was successfully resolved
    pub success: bool,
    /// Error message if resolution failed
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    /// Root package name
    pub root_package: String,
    /// All packages (root + dependencies)
    pub packages: Vec<PackageInfo>,
    /// All modules across all packages
    pub modules: Vec<ModuleInfo>,
}

pub fn execute(path: &Path) {
    let manifest = parse_manifest(path);
    let root_name = manifest.name.clone();

    // Resolve all dependencies to get the full module graph
    let mut resolver = DependencyResolver::new(path.to_path_buf());
    let graph = match resolver.resolve(&manifest) {
        Ok(g) => g,
        Err(e) => {
            output_err(&format!("Failed to resolve dependencies: {}", e));
            let output = ProjectMetadata {
                success: false,
                error: Some(format!("{}", e)),
                root_package: root_name,
                packages: vec![],
                modules: vec![],
            };
            println!("{}", serde_json::to_string(&output).unwrap());
            std::process::exit(1);
        }
    };

    // Build package info from graph nodes
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

        // Scan for modules in this package
        let src_dir = node.path.join("src");
        if src_dir.exists()
            && let Ok(modules) = scan_modules(name, &src_dir)
        {
            all_modules.extend(modules);
        }
    }

    // Sort for consistent output
    packages.sort_by(|a, b| a.name.cmp(&b.name));
    all_modules.sort_by(|a, b| a.name.cmp(&b.name));

    let output = ProjectMetadata {
        success: true,
        error: None,
        root_package: root_name,
        packages,
        modules: all_modules,
    };

    println!("{}", serde_json::to_string(&output).unwrap());
}

/// Scan a src directory for .soma modules
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
                format!("{}/{}", prefix, file_name_str)
            };
            scan_modules_recursive(package_name, &path, &new_prefix, modules)?;
        } else if path.extension().map(|e| e == "soma").unwrap_or(false) {
            let module_suffix = if prefix.is_empty() {
                file_name_str.trim_end_matches(".soma").to_string()
            } else {
                format!("{}/{}", prefix, file_name_str.trim_end_matches(".soma"))
            };

            let module_name = format!("{}/{}", package_name, module_suffix);
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
