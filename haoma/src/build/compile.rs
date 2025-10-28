use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::build::BuildResult;
use crate::build::errors::{BuildError, InternalBuildError};
use crate::build::graph::BuildNode;

pub fn compile_module(
    node: &BuildNode,
    _dependency_info: &HashMap<String, String>,
) -> Result<(PathBuf, Vec<PathBuf>), String> {
    let module_path = &node.path;
    let manifest = &node.manifest;
    let src_path = module_path.join("src");
    let build_path = module_path.join("build");

    fs::create_dir_all(&build_path)
        .map_err(|e| format!("Failed to create build directory: {}", e))?;
    let output_tarball = build_path.join(format!("{}.toria", &manifest.name));

    let mut command = Command::new("cabal");
    command
        .arg("run")
        .arg("soma")
        .arg("--project-dir=../")
        .arg("--")
        .arg(&src_path)
        .arg("--name")
        .arg(&manifest.name)
        .arg("--out")
        .arg(&output_tarball);

    for dep_name in &node.dependencies {
        let dep_tarball = node
            .path
            .parent()
            .map(|parent_dir| {
                parent_dir
                    .join(dep_name)
                    .join("build")
                    .join(format!("{}.toria", dep_name))
            })
            .ok_or_else(|| format!("Dependency tarball not found for '{}'", dep_name))?;

        command
            .arg("--dep")
            .arg(format!("{}={}", dep_name, dep_tarball.display()));
    }

    let status = command
        .status()
        .map_err(|e| format!("Failed to execute compiler: {}", e))?;

    if !status.success() {
        return Err(format!("Compilation failed for '{}'", manifest.name));
    }

    if !output_tarball.exists() {
        return Err(format!(
            "Compilation succeeded but output tarball not found: {}",
            output_tarball.display()
        ));
    }

    let objects_dir = build_path.join("objects");
    fs::create_dir_all(&objects_dir)
        .map_err(|e| format!("Failed to create objects directory: {}", e))?;

    extract_tarball(&output_tarball, &objects_dir)?;

    let object_paths = collect_object_files(&objects_dir)?;

    Ok((output_tarball, object_paths))
}

fn extract_tarball(tarball_path: &Path, dest_dir: &Path) -> Result<(), String> {
    use flate2::read::GzDecoder;
    use std::fs::File;

    let file = File::open(tarball_path).map_err(|e| format!("Failed to open tarball: {}", e))?;

    let decompressed = GzDecoder::new(file);
    let mut archive = tar::Archive::new(decompressed);

    archive
        .unpack(dest_dir)
        .map_err(|e| format!("Failed to extract tarball: {}", e))?;

    Ok(())
}

fn collect_object_files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut objects = Vec::new();

    if !dir.exists() {
        return Ok(objects);
    }

    collect_object_files_recursive(dir, &mut objects)?;

    Ok(objects)
}

fn collect_object_files_recursive(dir: &Path, objects: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries =
        fs::read_dir(dir).map_err(|e| format!("Failed to read objects directory: {}", e))?;

    for entry in entries {
        let entry = entry.map_err(|e| format!("Failed to read directory entry: {}", e))?;
        let path = entry.path();

        if path.is_file() && path.extension().and_then(|s| s.to_str()) == Some("o") {
            objects.push(path);
        } else if path.is_dir() {
            collect_object_files_recursive(&path, objects)?;
        }
    }

    Ok(())
}

pub fn link_executable(object_files: Vec<PathBuf>, output_path: &Path) -> BuildResult<()> {
    if object_files.is_empty() {
        return Err(BuildError::Internal(InternalBuildError::NoObjectsToLink));
    }

    let mut command = Command::new("clang");

    for object in &object_files {
        command.arg(object);
    }

    command
        .arg("-o")
        .arg(output_path)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::piped());

    let output = command
        .output()
        .map_err(BuildError::FailedToExecuteLinker)?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(BuildError::LinkingFailed(
            output.status.code().unwrap(),
            stderr.into_owned(),
        ));
    }

    if !output_path.exists() {
        return Err(BuildError::Internal(
            InternalBuildError::LinkingGeneratedNoOutput,
        ));
    }

    Ok(())
}
