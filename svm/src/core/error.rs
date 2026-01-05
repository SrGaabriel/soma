use std::path::PathBuf;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum SvmError {
    #[error("Version '{0}' is not installed")]
    VersionNotInstalled(String),

    #[error("Version '{0}' is already installed")]
    VersionAlreadyInstalled(String),

    #[error("No version is currently active")]
    NoActiveVersion,

    #[error("Cannot uninstall the currently active version '{0}'")]
    CannotUninstallActive(String),

    #[error("Build failed for component '{component}': {message}")]
    BuildFailed { component: String, message: String },

    #[error("Could not detect project root. Run from a Soma project directory or specify --path")]
    ProjectNotFound,

    #[error("Component '{0}' not found in project")]
    ComponentNotFound(String),

    #[error("Invalid svm.kdl configuration: {0}")]
    InvalidConfig(String),

    #[error("Invalid soma-toolchain.kdl: {0}")]
    InvalidToolchain(String),

    #[error("Incompatible versions: {0}")]
    IncompatibleVersions(String),

    #[error("Unsupported target: {0}")]
    UnsupportedTarget(String),

    #[error("Failed to setup shell: {0}")]
    ShellSetupFailed(String),

    #[error("IO error at {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },

    #[error("Remote downloads not yet implemented")]
    RemoteNotImplemented,
}

pub type Result<T> = std::result::Result<T, SvmError>;

impl SvmError {
    pub fn io(path: impl Into<PathBuf>, source: std::io::Error) -> Self {
        Self::Io {
            path: path.into(),
            source,
        }
    }
}
