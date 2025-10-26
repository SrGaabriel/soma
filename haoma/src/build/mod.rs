use std::{
    ops::Deref,
    path::{Path, PathBuf},
    process::Command,
    thread,
    time::Duration,
};

use colored::{Color, Colorize};
use indicatif::{ProgressBar, ProgressStyle};

use crate::{config::manifest::Manifest, logging::output_ok};

pub fn build_src(module_path: &Path, manifest: &Manifest) -> PathBuf {
    let src_path = module_path.join("src");
    let build_path = module_path.join("build");
    let output_object = build_path.join(format!("{}.o", &manifest.name));
    let output_executable = if cfg!(target_os = "windows") {
        build_path.join(format!("{}.exe", &manifest.name))
    } else {
        build_path.join(&manifest.name)
    };

    output_ok(&format!(
        "Running project '{}' version '{}'",
        manifest.name, manifest.version
    ));
    let build_spinner = ProgressBar::new_spinner();
    build_spinner.set_style(
        ProgressStyle::with_template(&format!(
            "{} {} {{msg}}",
            "[build]".color(Color::BrightCyan).bold(),
            "{spinner}".color(Color::Yellow)
        ))
        .unwrap()
        .tick_strings(&["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]),
    );
    build_spinner.set_message("Compiling source files...");
    let compilation_handle = {
        let output_object = output_object.clone();
        std::thread::spawn(move || {
            let mut binding = Command::new("cabal");
            let command = binding
                .arg("run")
                .arg("soma")
                .arg("--project-dir=../")
                .arg("--")
                .arg(src_path)
                .arg("--out")
                .arg(output_object);

            command.status().expect("failed to run command");
        })
    };

    while !compilation_handle.is_finished() {
        build_spinner.tick();
        thread::sleep(Duration::from_millis(100));
    }

    compilation_handle.join().unwrap();
    build_spinner.finish_with_message("Build finished!");
    output_ok("Project built successfully.");

    let linking_spinner = ProgressBar::new_spinner();
    linking_spinner.set_style(
        ProgressStyle::with_template(&format!(
            "{} {} {{msg}}",
            "[link]".color(Color::BrightCyan).bold(),
            "{spinner}".color(Color::Yellow)
        ))
        .unwrap()
        .tick_strings(&["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]),
    );
    linking_spinner.set_message("Linking object files...");

    let linking_handle = {
        let output_executable = output_executable.clone();
        std::thread::spawn(move || {
            let mut binding = Command::new("clang");
            let command = binding
                .arg(output_object.clone().deref())
                .arg("-o")
                .arg(output_executable.clone().deref())
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null());

            command.status().expect("failed to run command");
        })
    };

    while !linking_handle.is_finished() {
        linking_spinner.tick();
        thread::sleep(Duration::from_millis(100));
    }
    linking_handle.join().unwrap();
    linking_spinner.finish_with_message("Linking finished!");
    output_executable
}
