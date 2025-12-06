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
        }
    }
}

#[inline]
pub fn compiler_name() -> String {
    String::from(COMPILER_NAME)
}

