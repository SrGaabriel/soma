use crate::build::BuildResult;
use crate::build::consts::{
    BUILD_FOLDER_NAME, CONFIG_BUILD_FILE_NAME, CONFIG_FOLDER_NAME, SRC_FOLDER_NAME,
};
use crate::build::errors::{BuildError, InternalBuildError};
use crate::build::graph::BuildNode;
use crate::config::build::{BuildConfig, find_sysroot};
use crate::config::manifest::ManifestModuleType;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::process::Stdio;

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
    let src_path = module_path.join(SRC_FOLDER_NAME);
    let build_path = module_path.join(BUILD_FOLDER_NAME);

    fs::create_dir_all(&build_path).map_err(BuildError::FailedToCreateBuildDirectory)?;
    let output_file = build_path.join(output_filename);

    let build_config_path = module_path
        .join(CONFIG_FOLDER_NAME)
        .join(CONFIG_BUILD_FILE_NAME);
    let build_config = if build_config_path.exists() {
        toml::from_str::<BuildConfig>(
            &fs::read_to_string(&build_config_path)
                .map_err(BuildError::FailedToReadBuildConfigFile)?,
        )
        .map_err(|_| BuildError::FailedToParseBuildConfigFile(build_config_path))?
    } else {
        println!(
            "No build config found at: {}, using defaults",
            build_config_path.display()
        );
        BuildConfig::default()
    };

    let mut command = build_config.somac.to_command();
    command
        .arg(&src_path)
        .arg("--name")
        .arg(&manifest.name)
        .arg("--out")
        .arg(&output_file);
    if manifest.module_type == ManifestModuleType::Library {
        command.arg("--lib");
    };

    if let Some(sysroot) = find_sysroot(build_config.somac.sysroot.as_deref()) {
        command.arg("--sysroot").arg(sysroot);
    }

    command.stdout(Stdio::null()).stderr(Stdio::inherit());
    if let Some(debug_flag) = build_config.somac.debug
        && debug_flag
    {
        command.stdout(Stdio::inherit());
    }

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
