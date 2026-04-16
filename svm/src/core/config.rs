use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use crate::core::{Result, SvmError};

#[derive(Debug, Clone)]
pub struct ComponentConfig {
    pub name: String,
    pub path: PathBuf,
    pub build_command: String,
    pub binary_path: PathBuf,
}

/// Configuration for library/runtime files
#[derive(Debug, Clone)]
pub struct LibraryConfig {
    pub name: String,
    pub path: PathBuf,
    pub files: Vec<PathBuf>,
}

#[derive(Debug, Clone)]
pub struct BuildConfig {
    pub components: HashMap<String, ComponentConfig>,
    pub libraries: HashMap<String, LibraryConfig>,
}

impl BuildConfig {
    pub fn load(project_root: &Path) -> Result<Self> {
        let config_path = project_root.join("svm.kdl");
        if config_path.exists() {
            Self::from_kdl(&config_path)
        } else {
            Self::auto_detect(project_root)
        }
    }

    /// Parse svm.kdl configuration
    fn from_kdl(path: &Path) -> Result<Self> {
        let content = fs::read_to_string(path).map_err(|e| SvmError::io(path, e))?;
        let doc: kdl::KdlDocument = content
            .parse()
            .map_err(|e| SvmError::InvalidConfig(format!("{e}")))?;

        let mut components = HashMap::new();
        let mut libraries = HashMap::new();

        for node in doc.nodes() {
            let name = node.name().value().to_string();

            let get_string = |key: &str| -> Option<String> {
                node.children()?
                    .get(key)?
                    .entries()
                    .first()?
                    .value()
                    .as_string()
                    .map(std::string::ToString::to_string)
            };

            let get_string_array = |key: &str| -> Option<Vec<String>> {
                let children = node.children()?;
                let child = children.get(key)?;
                Some(
                    child
                        .entries()
                        .iter()
                        .filter_map(|e| e.value().as_string().map(std::string::ToString::to_string))
                        .collect(),
                )
            };

            // Check if this is a library config
            if let Some(files) = get_string_array("files") {
                let path_str = get_string("path")
                    .ok_or_else(|| SvmError::InvalidConfig(format!("Missing 'path' for {name}")))?;
                libraries.insert(
                    name.clone(),
                    LibraryConfig {
                        name,
                        path: PathBuf::from(path_str),
                        files: files.into_iter().map(PathBuf::from).collect(),
                    },
                );
            } else {
                let path_str = get_string("path")
                    .ok_or_else(|| SvmError::InvalidConfig(format!("Missing 'path' for {name}")))?;
                let build_command = get_string("build").ok_or_else(|| {
                    SvmError::InvalidConfig(format!("Missing 'build' for {name}"))
                })?;
                let binary_str = get_string("binary").ok_or_else(|| {
                    SvmError::InvalidConfig(format!("Missing 'binary' for {name}"))
                })?;

                components.insert(
                    name.clone(),
                    ComponentConfig {
                        name,
                        path: PathBuf::from(path_str),
                        build_command,
                        binary_path: PathBuf::from(binary_str),
                    },
                );
            }
        }

        Ok(Self {
            components,
            libraries,
        })
    }

    /// Auto-detect standard Soma project structure
    fn auto_detect(project_root: &Path) -> Result<Self> {
        let mut components = HashMap::new();
        let mut libraries = HashMap::new();

        // somac - Lean4 compiler
        let compiler_dir = project_root.join("compiler");
        if compiler_dir.exists() {
            components.insert(
                "somac".to_string(),
                ComponentConfig {
                    name: "somac".to_string(),
                    path: compiler_dir,
                    build_command: "lake build somac".to_string(),
                    binary_path: PathBuf::from(".lake/build/bin/somac"),
                },
            );
        }

        // haoma - Rust package manager
        let haoma_dir = project_root.join("haoma");
        if haoma_dir.exists() {
            components.insert(
                "haoma".to_string(),
                ComponentConfig {
                    name: "haoma".to_string(),
                    path: haoma_dir,
                    build_command: "cargo build --release".to_string(),
                    binary_path: PathBuf::from("target/release/haoma"),
                },
            );
        }

        // souls - Lean4 language server
        let souls_dir = project_root.join("souls");
        if souls_dir.exists() {
            components.insert(
                "souls".to_string(),
                ComponentConfig {
                    name: "souls".to_string(),
                    path: souls_dir,
                    build_command: "lake build souls".to_string(),
                    binary_path: PathBuf::from(".lake/build/bin/souls"),
                },
            );
        }

        let runtime_dir = project_root.join("runtime");
        if runtime_dir.exists() {
            libraries.insert(
                "runtime".to_string(),
                LibraryConfig {
                    name: "runtime".to_string(),
                    path: runtime_dir,
                    files: vec![
                        PathBuf::from("soma_runtime.zig"),
                        PathBuf::from("build.zig"),
                    ],
                },
            );
        }

        if components.is_empty() {
            return Err(SvmError::ProjectNotFound);
        }

        Ok(Self {
            components,
            libraries,
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = &ComponentConfig> {
        self.components.values()
    }

    pub fn iter_libraries(&self) -> impl Iterator<Item = &LibraryConfig> {
        self.libraries.values()
    }
}
