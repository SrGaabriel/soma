use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde::{Deserialize, Serialize};

use crate::build::consts::SRC_FOLDER_NAME;
use crate::build::graph::BuildNode;
use crate::build::resolve::DependencyResolver;
use crate::cli::parse_manifest;
use crate::cli::somac;
use crate::logging::{output_err, output_ok};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckOutput {
    pub success: bool,
    pub diagnostics: Option<String>,
    #[serde(rename = "module")]
    pub module_name: Option<String>,
}

pub fn execute(path: &Path) {
    let manifest = parse_manifest(path);

    let mut resolver = DependencyResolver::new(path.to_path_buf());
    let graph = match resolver.resolve(&manifest) {
        Ok(g) => g,
        Err(e) => {
            output_err(&format!("Failed to resolve dependencies: {e}"));
            std::process::exit(1);
        }
    };

    let layers = match graph.topological_layers() {
        Ok(l) => l,
        Err(e) => {
            output_err(&format!("Failed to order modules: {e}"));
            std::process::exit(1);
        }
    };

    let mut all_outputs = Vec::new();
    let mut all_success = true;
    let mut dep_metadata: HashMap<String, PathBuf> = HashMap::new();

    let root_module = layers.last().and_then(|l| l.last()).cloned();

    for layer in layers {
        for module_name in layer {
            if let Some(node) = graph.get_node(&module_name) {
                let dep_files: HashMap<String, PathBuf> = node
                    .dependencies
                    .iter()
                    .filter_map(|dep| dep_metadata.get(dep).map(|p| (dep.clone(), p.clone())))
                    .collect();

                let is_root = root_module.as_ref() == Some(&module_name);

                if is_root {
                    match check_module(node, &dep_files) {
                        Ok(output) => {
                            if !output.success {
                                all_success = false;
                            }
                            all_outputs.push(output);
                        }
                        Err(e) => {
                            all_success = false;
                            all_outputs.push(make_error_output(node, &module_name, &e));
                        }
                    }
                } else {
                    match somac::generate_metadata(node, &dep_files) {
                        Ok(metadata_path) => {
                            all_outputs.push(CheckOutput {
                                success: true,
                                diagnostics: None,
                                module_name: Some(module_name.clone()),
                            });
                            dep_metadata.insert(module_name.clone(), metadata_path);
                        }
                        Err(e) => {
                            all_success = false;
                            all_outputs.push(make_error_output(
                                node,
                                &module_name,
                                &format!("Failed to generate metadata for dependency: {e}"),
                            ));
                        }
                    }
                }
            }
        }
    }

    for module_output in all_outputs {
        if let Some(module_name) = &module_output.module_name {
            if module_output.success {
                output_ok(&format!("Module '{module_name}': Check passed"));
            } else {
                output_err(&format!("Module '{module_name}': Check failed"));
            }
            if let Some(diagnostics) = &module_output.diagnostics {
                println!("{diagnostics}");
            }
        }
    }

    if !all_success {
        output_err("One or more checks failed. Please review the diagnostics above.");
        std::process::exit(1);
    }
    output_ok("All checks passed successfully!");
}

fn make_error_output(_node: &BuildNode, module_name: &str, message: &str) -> CheckOutput {
    CheckOutput {
        success: false,
        diagnostics: Some(message.to_string()),
        module_name: Some(module_name.to_string()),
    }
}

fn check_module(
    node: &BuildNode,
    dependency_metadata: &HashMap<String, PathBuf>,
) -> Result<CheckOutput, String> {
    let src_path = node
        .path
        .join(SRC_FOLDER_NAME)
        .canonicalize()
        .map_err(|e| format!("Failed to canonicalize src path: {e}"))?;

    let mut command = Command::new("somac");
    if std::env::var("LEAN_STACK_SIZE").is_err() {
        command.env("LEAN_STACK_SIZE", "32768");
    }
    command
        .arg("check")
        .arg(&src_path)
        .arg("--name")
        .arg(&node.manifest.name)
        .arg("--format=human")
        .stdout(Stdio::null())
        .stderr(Stdio::piped());

    for (dep_name, dep_path) in dependency_metadata {
        let meta_path = dep_path.canonicalize().unwrap_or_else(|_| dep_path.clone());
        command
            .arg("--dep")
            .arg(format!("{}={}", dep_name, meta_path.display()));
    }

    let output = command
        .output()
        .map_err(|e| format!("Failed to run compiler: {e}"))?;

    let stderr = String::from_utf8_lossy(&output.stderr);

    Ok(CheckOutput {
        success: output.status.success(),
        diagnostics: if stderr.trim().is_empty() {
            None
        } else {
            Some(stderr.trim().to_string())
        },
        module_name: Some(node.manifest.name.clone()),
    })
}
