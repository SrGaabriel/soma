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
use std::path::{Path, PathBuf};
use std::process::Stdio;

#[cfg(windows)]
fn strip_unc_prefix(path: &Path) -> PathBuf {
    let path_str = path.to_string_lossy();
    if let Some(stripped) = path_str.strip_prefix(r"\\?\") {
        PathBuf::from(stripped)
    } else {
        path.to_path_buf()
    }
}

#[cfg(not(windows))]
fn strip_unc_prefix(path: &Path) -> PathBuf {
    path.to_path_buf()
}

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
    let platform_suffix = if cfg!(target_os = "windows") {
        ".exe"
    } else {
        ""
    };
    let output_filename = format!("{}{}", node.manifest.name, platform_suffix);
    compile_module(node, dependency_tarballs, output_filename)
}

fn compile_module(
    node: &BuildNode,
    dependency_tarballs: &HashMap<String, PathBuf>,
    output_filename: String,
) -> BuildResult<PathBuf> {
    let module_path = &node.path;
    let manifest = &node.manifest;
    let src_path = strip_unc_prefix(&module_path.join(SRC_FOLDER_NAME));
    let build_path = module_path.join(BUILD_FOLDER_NAME);

    fs::create_dir_all(&build_path).map_err(BuildError::FailedToCreateBuildDirectory)?;
    let output_file = strip_unc_prefix(&build_path.join(output_filename));

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
        BuildConfig::default()
    };

    let mut command = build_config.somac.to_command();
    if std::env::var("LEAN_STACK_SIZE").is_err() {
        command.env("LEAN_STACK_SIZE", "32768");
    }
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
    let verbose =
        std::env::var("SOMA_VERBOSE_LOGGING").is_ok() || build_config.somac.debug.unwrap_or(false);

    command.stdout(Stdio::null()).stderr(Stdio::inherit());
    if verbose {
        command.stdout(Stdio::inherit());
    }

    if let Ok(profile) = std::env::var("SOMA_PROFILE") {
        command.arg("--profile").arg(profile);
    }

    let emit_llvm_from_config = build_config.somac.emit_llvm.unwrap_or(false);
    let emit_llvm_from_env = std::env::var("SOMA_EMIT_LLVM").is_ok();
    if emit_llvm_from_config || emit_llvm_from_env {
        command.arg("--emit-llvm");
    }

    // Pass all dependencies as a single comma-separated --dep argument
    // The somac CLI expects: --dep "name1=path1,name2=path2"
    if !dependency_tarballs.is_empty() {
        let deps_str: Vec<String> = dependency_tarballs
            .iter()
            .map(|(name, path)| format!("{}={}", name, strip_unc_prefix(path).display()))
            .collect();
        command.arg("--dep").arg(deps_str.join(","));
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
