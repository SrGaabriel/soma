use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde::{Deserialize, Serialize};

use crate::build::graph::BuildNode;
use crate::build::resolve::DependencyResolver;
use crate::cli::parse_manifest;
use crate::logging::output_err;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Diagnostic {
    pub file: String,
    pub range: Range,
    pub severity: u32,
    pub message: String,
    pub source: String,
    pub code: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckOutput {
    pub success: bool,
    pub diagnostics: Vec<Diagnostic>,
    #[serde(rename = "module")]
    pub module_name: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProjectCheckOutput {
    pub success: bool,
    pub modules: Vec<CheckOutput>,
}

pub fn execute(path: &Path) {
    let manifest = parse_manifest(path);

    let mut resolver = DependencyResolver::new(path.to_path_buf());
    let graph = match resolver.resolve(&manifest) {
        Ok(g) => g,
        Err(e) => {
            output_err(&format!("Failed to resolve dependencies: {}", e));
            let output = ProjectCheckOutput {
                success: false,
                modules: vec![],
            };
            println!("{}", serde_json::to_string(&output).unwrap());
            std::process::exit(1);
        }
    };

    let layers = match graph.topological_layers() {
        Ok(l) => l,
        Err(e) => {
            output_err(&format!("Failed to order modules: {}", e));
            let output = ProjectCheckOutput {
                success: false,
                modules: vec![],
            };
            println!("{}", serde_json::to_string(&output).unwrap());
            std::process::exit(1);
        }
    };

    let mut all_outputs = Vec::new();
    let mut all_success = true;
    let mut built_tarballs: HashMap<String, PathBuf> = HashMap::new();

    for layer in layers {
        for module_name in layer {
            if let Some(node) = graph.get_node(&module_name) {
                let dep_tarballs: HashMap<String, PathBuf> = node
                    .dependencies
                    .iter()
                    .filter_map(|dep| built_tarballs.get(dep).map(|p| (dep.clone(), p.clone())))
                    .collect();

                match check_module(node, &dep_tarballs) {
                    Ok(output) => {
                        if !output.success {
                            all_success = false;
                        }
                        all_outputs.push(output);

                        let tarball_path = node
                            .path
                            .join("build")
                            .join(format!("{}.toria", node.manifest.name));
                        if tarball_path.exists() {
                            built_tarballs.insert(module_name.clone(), tarball_path);
                        }
                    }
                    Err(e) => {
                        all_success = false;
                        all_outputs.push(CheckOutput {
                            success: false,
                            diagnostics: vec![Diagnostic {
                                file: node.path.join("src").to_string_lossy().to_string(),
                                range: Range {
                                    start: Position {
                                        line: 0,
                                        character: 0,
                                    },
                                    end: Position {
                                        line: 0,
                                        character: 0,
                                    },
                                },
                                severity: 1,
                                message: format!("Failed to check module: {}", e),
                                source: "haoma".to_string(),
                                code: None,
                            }],
                            module_name: Some(module_name.clone()),
                        });
                    }
                }
            }
        }
    }

    let project_output = ProjectCheckOutput {
        success: all_success,
        modules: all_outputs,
    };

    println!("{}", serde_json::to_string(&project_output).unwrap());

    if !all_success {
        std::process::exit(1);
    }
}

fn check_module(
    node: &BuildNode,
    dependency_tarballs: &HashMap<String, PathBuf>,
) -> Result<CheckOutput, String> {
    let src_path = node
        .path
        .join("src")
        .canonicalize()
        .map_err(|e| format!("Failed to canonicalize src path: {}", e))?;

    let mut command = Command::new("cabal");
    command
        .arg("run")
        .arg("compiler")
        .arg("--")
        .arg("check")
        .arg(&src_path)
        .arg("--name")
        .arg(&node.manifest.name)
        .arg("--format=json")
        .stdout(Stdio::piped())
        .stderr(Stdio::null());

    for (dep_name, dep_tarball) in dependency_tarballs {
        let tarball_path = dep_tarball
            .canonicalize()
            .unwrap_or_else(|_| dep_tarball.clone());
        command
            .arg("--dep")
            .arg(format!("{}={}", dep_name, tarball_path.display()));
    }

    let output = command
        .output()
        .map_err(|e| format!("Failed to run compiler: {}", e))?;

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Parse JSON output from soma - find the first line that starts with '{'
    let json_line = stdout
        .lines()
        .find(|line| line.trim().starts_with('{'))
        .unwrap_or(&stdout);

    serde_json::from_str(json_line).map_err(|e| {
        format!(
            "Failed to parse compiler output: {} (output was: {})",
            e, stdout
        )
    })
}
