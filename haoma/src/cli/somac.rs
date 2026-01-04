use std::collections::HashMap;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use crate::build::consts::{BUILD_FOLDER_NAME, SRC_FOLDER_NAME};
use crate::build::graph::BuildNode;

pub fn generate_metadata(
    node: &BuildNode,
    dependency_metadata: &HashMap<String, PathBuf>,
) -> Result<PathBuf, String> {
    let src_path = node
        .path
        .join(SRC_FOLDER_NAME)
        .canonicalize()
        .map_err(|e| format!("Failed to canonicalize src path: {}", e))?;

    let build_folder = node.path.join(BUILD_FOLDER_NAME);
    std::fs::create_dir_all(&build_folder)
        .map_err(|e| format!("Failed to create build folder: {}", e))?;

    let metadata_path = build_folder.join(format!("{}.meta.json", node.manifest.name));

    let mut command = Command::new("somac");
    command
        .arg("metadata")
        .arg(&src_path)
        .arg("--name")
        .arg(&node.manifest.name)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    for (dep_name, dep_path) in dependency_metadata {
        let meta_path = dep_path.canonicalize().unwrap_or_else(|_| dep_path.clone());
        command
            .arg("--dep")
            .arg(format!("{}={}", dep_name, meta_path.display()));
    }

    let output = command
        .output()
        .map_err(|e| format!("Failed to run somac metadata: {}", e))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        return Err(format!(
            "somac metadata failed for '{}': {}\n{}",
            node.manifest.name,
            stderr.trim(),
            stdout.trim()
        ));
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json_line = stdout
        .lines()
        .find(|line| line.trim().starts_with('{'))
        .ok_or_else(|| {
            format!(
                "No JSON output from somac metadata for '{}'",
                node.manifest.name
            )
        })?;

    std::fs::write(&metadata_path, json_line)
        .map_err(|e| format!("Failed to write metadata file: {}", e))?;

    Ok(metadata_path)
}

pub fn generate_all_metadata(
    graph: &crate::build::graph::DependencyGraph,
) -> Result<HashMap<String, PathBuf>, String> {
    let layers = graph
        .topological_layers()
        .map_err(|e| format!("Failed to order packages: {}", e))?;

    let mut metadata_paths: HashMap<String, PathBuf> = HashMap::new();

    for layer in layers {
        for package_name in layer {
            if let Some(node) = graph.get_node(&package_name) {
                let dep_metadata: HashMap<String, PathBuf> = node
                    .dependencies
                    .iter()
                    .filter_map(|dep| metadata_paths.get(dep).map(|p| (dep.clone(), p.clone())))
                    .collect();

                let metadata_path = generate_metadata(node, &dep_metadata)?;
                metadata_paths.insert(package_name, metadata_path);
            }
        }
    }

    Ok(metadata_paths)
}
