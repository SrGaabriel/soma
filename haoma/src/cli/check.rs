use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use serde::{Deserialize, Serialize};

use crate::build::consts::SRC_FOLDER_NAME;
use crate::build::graph::BuildNode;
use crate::build::resolve::DependencyResolver;
use crate::cli::parse_manifest;
use crate::cli::somac;
use crate::logging::output_err;
use crate::style::{self, Tone};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckOutput {
    pub success: bool,
    pub diagnostics: Option<String>,
    #[serde(rename = "module")]
    pub module_name: Option<String>,
}

pub fn execute(path: &Path) {
    let manifest = parse_manifest(path);
    let started = Instant::now();

    let mut resolver = DependencyResolver::new(path.to_path_buf());
    let graph = match resolver.resolve(&manifest) {
        Ok(g) => g,
        Err(e) => {
            output_err(format!("failed to resolve dependencies: {e}"));
            std::process::exit(1);
        }
    };

    let layers = match graph.topological_layers() {
        Ok(l) => l,
        Err(e) => {
            output_err(format!("failed to order modules: {e}"));
            std::process::exit(1);
        }
    };

    let mut all_outputs = Vec::new();
    let mut all_success = true;
    let mut dep_metadata: HashMap<String, PathBuf> = HashMap::new();

    let root_module = layers.last().and_then(|l| l.last()).cloned();

    for layer in &layers {
        for module_name in layer {
            let Some(node) = graph.get_node(module_name) else {
                continue;
            };
            let dep_files: HashMap<String, PathBuf> = node
                .dependencies
                .iter()
                .filter_map(|dep| dep_metadata.get(dep).map(|p| (dep.clone(), p.clone())))
                .collect();

            let is_root = root_module.as_ref() == Some(module_name);
            if style::is_verbose() {
                style::status(Tone::Progress, "checking", module_name);
            }

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
                        all_outputs.push(make_error_output(node, module_name, &e));
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
                            module_name,
                            &format!("failed to generate metadata for dependency: {e}"),
                        ));
                    }
                }
            }
        }
    }

    let module_count = all_outputs.len();
    let mut failed = 0usize;
    for module_output in &all_outputs {
        if !module_output.success {
            failed += 1;
            if let Some(name) = &module_output.module_name {
                output_err(format!("check failed for `{name}`"));
            }
            if let Some(diagnostics) = &module_output.diagnostics {
                eprintln!("{diagnostics}");
            }
        }
    }

    let elapsed = format_duration(started.elapsed().as_millis());
    if all_success {
        style::status(
            Tone::Success,
            "checked",
            format!("· {module_count} modules · {elapsed}"),
        );
    } else {
        println!(
            "{}",
            style::format_status(
                Tone::Error,
                "failed",
                format!("· {failed}/{module_count} · {elapsed}")
            )
        );
        std::process::exit(1);
    }
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

#[allow(clippy::cast_precision_loss)]
fn format_duration(ms: u128) -> String {
    if ms < 1000 {
        format!("{ms}ms")
    } else if ms < 60_000 {
        format!("{:.2}s", ms as f64 / 1000.0)
    } else {
        let seconds = ms / 1000;
        let minutes = seconds / 60;
        let remaining_seconds = seconds % 60;
        format!("{minutes}m {remaining_seconds}s")
    }
}
