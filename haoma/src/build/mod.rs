mod cache;
mod compile;
pub mod consts;
mod errors;
pub mod graph;
mod orchestrator;
mod progress;
pub mod resolve;
mod scheduler;

use orchestrator::BuildOrchestrator;
pub use orchestrator::BuildStats; // just so it's prettier
use std::path::Path;

use crate::{build::errors::BuildError, config::manifest::Manifest};

pub type BuildResult<T> = Result<T, BuildError>;

pub fn build_project(module_path: &Path, manifest: &Manifest) -> BuildResult<BuildStats> {
    let mut orchestrator = BuildOrchestrator::new(module_path.to_path_buf())?;
    orchestrator.build(manifest)
}

pub fn clean_project(module_path: &Path) -> BuildResult<u64> {
    let mut orchestrator = BuildOrchestrator::new(module_path.to_path_buf())?;
    orchestrator.clean()
}
