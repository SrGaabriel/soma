#[derive(Debug, thiserror::Error)]
pub enum BuildError {
    #[error("Internal build error: {0}")]
    Internal(InternalBuildError),
    #[error("Failed to read cache: {0}")]
    FailedToSaveCache(std::io::Error),
    #[error("Failed to write cache: {0}")]
    FailedToCleanBuildArtifacts(std::io::Error),
    #[error("Build cache is unavailable: {0}")]
    UnavailableBuildCache(std::io::Error),
    #[error("Failed to create build directory: {0}")]
    FailedToCreateBuildDirectory(std::io::Error),
    #[error("Compilation failed for module '{0}'")]
    CompilationFailed(String),
    #[error("Circular dependency detected involving module '{0}'")]
    CircularDependencyDetected(String),
    #[error("The dependency '{missing_dependency}' required by module '{module}' was not found")]
    DependencyNotFound {
        module: String,
        missing_dependency: String,
    },
    #[error("Dependency graph is not acyclic")]
    GraphIsNotAcyclic,
    #[error(
        "The local dependency '{missing_dependency}' required by module '{module}' was not found at '{missing_dependency_path}'"
    )]
    LocalDependencyNotFound {
        module: String,
        missing_dependency: String,
        missing_dependency_path: String,
    },
    #[error(
        "Dependency name conflict: expected '{expected_name}', found '{found_name}' at path '{dep_path}'(required by '{module}')"
    )]
    LocalDependencyModuleNameMismatch {
        module: String,
        expected_name: String,
        found_name: String,
        dep_path: String,
    },
    #[error(
        "The local dependency '{dependency}' for module '{module}' has a version mismatch: expected '{expected_version}', found '{found_version}' at path '{dep_path}'"
    )]
    LocalDependencyModuleVersionMismatch {
        module: String,
        dependency: String,
        expected_version: String,
        found_version: String,
        dep_path: String,
    },
    #[error("Registry dependencies are not supported: {0}")]
    RegistryDependenciesNotSupported(String),
    #[error("Duplicate module '{module}' found at paths '{existing_path}' and '{duplicate_path}'")]
    DuplicateModule {
        module: String,
        existing_path: String,
        duplicate_path: String,
    },
    #[error("Failed to resolve local dependency path '{dep_path}': {err}")]
    UnresolvedLocalDependencyPath {
        dep_path: String,
        err: std::io::Error,
    },
    #[error("Failed to call compiler. Is it installed and in your PATH? Error: {0}")]
    FailedToCallCompiler(std::io::Error),
}

#[derive(Debug, thiserror::Error)]
pub enum InternalBuildError {
    #[error("Unexpected scheduler receiver shutdown: {0}")]
    UnexpectedSchedulerReceiverShutdown(String),
    #[error("Build node not found: {0}")]
    BuildNodeNotFound(String),
    #[error("Failed to receive build result")]
    FailedToReceiveBuildResult,
    #[error("Unexpected layer build failure: {0}")]
    UnexpectedLayerBuildFailure(usize),
    #[error("Module hash not found: {0}")]
    ModuleHashNotFound(String),
    #[error("Compilation produced no output for module: {0}")]
    CompilationProducedNoOutput(String),
}
