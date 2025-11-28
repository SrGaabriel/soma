use crate::build::BuildResult;
use crate::build::errors::{BuildError, InternalBuildError};
use crate::build::graph::BuildNode;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};

pub fn compile_lib(
    node: &BuildNode,
    dependency_tarballs: &HashMap<String, PathBuf>,
) -> BuildResult<PathBuf> {
    compile_module(
        node,
        dependency_tarballs,
        format!("{}.toria", node.manifest.name),
    )
}

pub fn compile_binary(
    node: &BuildNode,
    dependency_tarballs: &HashMap<String, PathBuf>,
) -> BuildResult<PathBuf> {
    compile_module(node, dependency_tarballs, node.name.clone())
}

fn compile_module(
    node: &BuildNode,
    dependency_tarballs: &HashMap<String, PathBuf>,
    output_filename: String,
) -> BuildResult<PathBuf> {
    let module_path = &node.path;
    let manifest = &node.manifest;
    let src_path = module_path.join("src");
    let build_path = module_path.join("build");

    fs::create_dir_all(&build_path).map_err(BuildError::FailedToCreateBuildDirectory)?;
    let output_file = build_path.join(output_filename);

    let mut command = Command::new("somac");
    command
        .arg(&src_path)
        .arg("--name")
        .arg(&manifest.name)
        .arg("--out")
        .stdout(Stdio::null())
        .stderr(Stdio::inherit())
        .arg(&output_file);

    for (dep_name, dep_tarball) in dependency_tarballs {
        command
            .arg("--dep")
            .arg(format!("{}={}", dep_name, dep_tarball.display()));
    }

    let output = command.output().map_err(BuildError::FailedToCallCompiler)?;

    if !output.status.success() {
        return Err(BuildError::CompilationFailed(manifest.name.clone()));
    }

    if !output_file.exists() {
        return Err(BuildError::Internal(
            InternalBuildError::CompilationProducedNoOutput(manifest.name.clone()),
        ));
    }

    Ok(output_file)
}
