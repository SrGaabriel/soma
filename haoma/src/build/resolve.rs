use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::build::BuildResult;
use crate::build::errors::BuildError;
use crate::build::graph::{BuildNode, DependencyGraph};
use crate::cli::parse_manifest;
use crate::config::manifest::{Manifest, ManifestDependencyValue, ManifestModuleType};

pub struct DependencyResolver {
    root_path: PathBuf,
    visited: HashMap<String, PathBuf>,
}

impl DependencyResolver {
    pub fn new(root_path: PathBuf) -> Self {
        Self {
            root_path,
            visited: HashMap::new(),
        }
    }

    pub fn resolve(&mut self, root_manifest: &Manifest) -> BuildResult<DependencyGraph> {
        let mut graph = DependencyGraph::new();

        self.resolve_recursive(&self.root_path.clone(), root_manifest, &mut graph)?;
        graph.validate()?;

        Ok(graph)
    }

    fn resolve_recursive(
        &mut self,
        module_path: &Path,
        manifest: &Manifest,
        graph: &mut DependencyGraph,
    ) -> BuildResult<()> {
        let module_name = manifest.name.clone();

        if self.visited.contains_key(&module_name) {
            let existing_path = self.visited.get(&module_name).unwrap();
            if existing_path != module_path {
                return Err(BuildError::DuplicateModule {
                    module: module_name.clone(),
                    existing_path: existing_path.display().to_string(),
                    duplicate_path: module_path.display().to_string(),
                });
            }
            return Ok(());
        }

        self.visited
            .insert(module_name.clone(), module_path.to_path_buf());

        let mut dependency_names = Vec::new();
        for (dep_name, dep_value) in &manifest.dependencies.dependencies {
            match dep_value {
                ManifestDependencyValue::Custom { path, version } => {
                    let dep_path = self.resolve_path(module_path, path)?;

                    if !dep_path.exists() {
                        return Err(BuildError::LocalDependencyNotFound {
                            module: module_name.clone(),
                            missing_dependency: dep_name.clone(),
                            missing_dependency_path: dep_path.display().to_string(),
                        });
                    }

                    let dep_manifest = parse_manifest(&dep_path);
                    if dep_manifest.name != *dep_name {
                        return Err(BuildError::LocalDependencyModuleNameMismatch {
                            module: module_name.clone(),
                            expected_name: dep_name.clone(),
                            found_name: dep_manifest.name,
                            dep_path: dep_path.display().to_string(),
                        });
                    }
                    
                    if dep_manifest.module_type != ManifestModuleType::Library {
                        return Err(BuildError::LocalDependencyNotALibrary {
                            module: module_name.clone(),
                            dependency: dep_name.clone(),
                            dep_path: dep_path.display().to_string(),
                        });
                    }

                    if let Some(expected_version) = version
                        && dep_manifest.version != *expected_version
                    {
                        return Err(BuildError::LocalDependencyModuleVersionMismatch {
                            module: module_name.clone(),
                            dependency: dep_name.clone(),
                            expected_version: expected_version.clone(),
                            found_version: dep_manifest.version,
                            dep_path: dep_path.display().to_string(),
                        });
                    }
                    
                    dependency_names.push(dep_name.clone());
                    self.resolve_recursive(&dep_path, &dep_manifest, graph)?;
                }
                ManifestDependencyValue::Version(_version) => {
                    return Err(BuildError::RegistryDependenciesNotSupported(
                        dep_name.clone(),
                    ));
                }
            }
        }

        let node = BuildNode {
            name: module_name.clone(),
            path: module_path.to_path_buf(),
            manifest: manifest.clone(),
            dependencies: dependency_names,
        };
        graph.add_node(node);
        Ok(())
    }

    fn resolve_path(&self, base_path: &Path, relative_path: &str) -> BuildResult<PathBuf> {
        let path = Path::new(relative_path);
        if path.is_absolute() {
            return Ok(path.to_path_buf());
        }

        let resolved = base_path.join(path);
        resolved
            .canonicalize()
            .or_else(|_: std::io::Error| Ok::<PathBuf, std::io::Error>(resolved.clone()))
            .map_err(|e| BuildError::UnresolvedLocalDependencyPath {
                dep_path: relative_path.to_string(),
                err: e,
            })
    }
}
