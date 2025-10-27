mod deps;
mod metadata;

use std::{
    path::{Path, PathBuf},
    process::Command,
};

use crate::{
    build::deps::{DependencyAction, extract_deps},
    config::manifest::Manifest,
};

pub enum BuildOutput {
    Tarball,
    Object,
}

pub fn build_src(module_path: &Path, manifest: &Manifest, output_type: BuildOutput) -> PathBuf {
    let src_path = module_path.join("src");
    let build_path = module_path.join("build");
    let build_output = match output_type {
        BuildOutput::Tarball => build_path.join(format!("{}.toria", &manifest.name)),
        BuildOutput::Object => build_path.join(format!("{}.o", &manifest.name)),
    };
    let deps = extract_deps(manifest.name.to_string(), &manifest.dependencies);

    let dep_additions = deps
        .into_iter()
        .map(|dep| match dep {
            DependencyAction::Include {
                name,
                tarball,
                objects,
            } => (name, tarball, objects),
            _ => todo!(),
        })
        .collect::<Vec<(String, PathBuf, Vec<PathBuf>)>>();

    let compilation_handle = {
        let manifest_name = manifest.name.clone();
        let output_object = build_output.clone();
        let deps = dep_additions.clone();
        std::thread::spawn(move || {
            let mut binding = Command::new("cabal");
            let command = binding
                .arg("run")
                .arg("soma")
                .arg("--project-dir=../")
                .arg("--")
                .arg(src_path)
                .arg("--name")
                .arg(manifest_name)
                .arg("--out")
                .arg(output_object);

            for (dep_name, toria_path, _) in deps {
                command
                    .arg("--dep")
                    .arg(format!("{}={}", dep_name, toria_path.display()));
            }

            command.status().expect("failed to run command");
        })
    };
    compilation_handle.join().unwrap();
    if let BuildOutput::Tarball = output_type {
        return build_output;
    }

    let output_executable = build_path.join(&manifest.name);
    let objects = dep_additions
        .into_iter()
        .flat_map(|(_, _, objects)| objects)
        .chain(std::iter::once(build_output))
        .collect::<Vec<PathBuf>>();
    let linking_handle = {
        let output_executable = output_executable.clone();
        std::thread::spawn(move || {
            generate_executable(objects, &output_executable);
        })
    };
    linking_handle.join().unwrap();
    output_executable
}

pub fn generate_executable(objects: Vec<PathBuf>, output_executable: &PathBuf) {
    let mut binding = Command::new("clang");

    for object in objects {
        binding.arg(object);
    }

    binding
        .arg("-o")
        .arg(output_executable)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());

    binding.status().expect("failed to run command");
}
