use std::path::PathBuf;
use std::process::Command;

use crate::build::consts::COMPILER_NAME;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, Clone, Default)]
pub struct BuildConfig {
    #[serde(default)]
    pub somac: SomacBuildConfig,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct SomacBuildConfig {
    #[serde(default = "compiler_name")]
    pub binary: String,
    #[serde(default)]
    pub command: Option<String>,
    #[serde(default)]
    pub debug: Option<bool>,
    #[serde(default)]
    pub sysroot: Option<String>,
}

impl SomacBuildConfig {
    pub fn to_command(&self) -> Command {
        match &self.command {
            Some(cmd) => {
                let cmd_parts: Vec<&str> = cmd.split_whitespace().collect();
                let mut command = Command::new(cmd_parts[0]);
                if cmd_parts.len() > 1 {
                    command.args(&cmd_parts[1..]);
                }
                command
            }
            None => Command::new(&self.binary),
        }
    }
}

impl Default for SomacBuildConfig {
    fn default() -> Self {
        SomacBuildConfig {
            binary: compiler_name(),
            debug: None,
            command: None,
            sysroot: None,
        }
    }
}

#[inline]
pub fn compiler_name() -> String {
    String::from(COMPILER_NAME)
}

pub fn find_sysroot(config_sysroot: Option<&str>) -> Option<PathBuf> {
    if let Some(s) = config_sysroot {
        let path = PathBuf::from(s);
        if path.exists() {
            return Some(path);
        }
    }

    if let Ok(s) = std::env::var("SOMA_SYSROOT") {
        let path = PathBuf::from(s);
        if path.exists() {
            return Some(path);
        }
    }

    if let Ok(somac_path) = which::which("somac") {
        if let Some(bin_dir) = somac_path.parent() {
            if let Some(sysroot) = bin_dir.parent() {
                let lib_path = sysroot.join("lib");
                if lib_path.exists() {
                    return Some(sysroot.to_path_buf());
                }
            }
        }
    }

    if let Some(home) = dirs::home_dir() {
        let target = if cfg!(target_os = "windows") {
            "x86_64-windows"
        } else if cfg!(target_os = "macos") {
            if cfg!(target_arch = "aarch64") {
                "aarch64-macos"
            } else {
                "x86_64-macos"
            }
        } else {
            "x86_64-linux"
        };
        let svm_path = home.join(".svm").join("current").join(target);
        if svm_path.exists() {
            return Some(svm_path);
        }
    }

    None
}
