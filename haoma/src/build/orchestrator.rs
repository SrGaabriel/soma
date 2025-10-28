use std::collections::HashMap;
use std::path::PathBuf;
use std::time::Instant;

use crate::build::BuildResult;
use crate::build::cache::{BuildCache, CacheEntry, HashCalculator};
use crate::build::compile::link_executable;
use crate::build::errors::{BuildError, InternalBuildError};
use crate::build::graph::DependencyGraph;
use crate::build::resolve::DependencyResolver;
use crate::build::scheduler::{BuildResults, LayeredBuilder};
use crate::config::manifest::{Manifest, ManifestModuleType};

pub struct BuildOrchestrator {
    root_path: PathBuf,
    cache: BuildCache,
    num_workers: usize,
}

#[derive(Debug)]
#[allow(dead_code)]
pub struct BuildStats {
    pub final_binary_path: Option<PathBuf>,
    pub total_modules: usize,
    pub modules_built: usize,
    pub modules_cached: usize,
    pub total_time_ms: u128,
    pub resolution_time_ms: u128,
    pub analysis_time_ms: u128,
    pub execution_time_ms: u128,
    pub linking_time_ms: u128,
}

impl BuildOrchestrator {
    pub fn new(root_path: PathBuf) -> BuildResult<Self> {
        let cache_dir = root_path.join("build").join(".cache");
        let cache = BuildCache::load(&cache_dir)?;

        let num_workers = num_cpus::get().max(1);

        Ok(Self {
            root_path,
            cache,
            num_workers,
        })
    }

    pub fn build(&mut self, manifest: &Manifest) -> BuildResult<BuildStats> {
        let build_start = Instant::now();

        println!("╔═══════════════════════════════════════════════════════╗");
        println!("║           Build Orchestrator - Modern Build          ║");
        println!("╚═══════════════════════════════════════════════════════╝\n");

        println!("┌─────────────────────────────────────────────────────┐");
        println!("│ Phase 1: Dependency Resolution                      │");
        println!("└─────────────────────────────────────────────────────┘");

        let resolution_start = Instant::now();
        let graph = self.resolve_dependencies(manifest)?;
        let resolution_time = resolution_start.elapsed().as_millis();

        println!("  ✓ Resolved {} modules", graph.len());
        println!("  ⏱  {}ms\n", resolution_time);

        println!("┌─────────────────────────────────────────────────────┐");
        println!("│ Phase 2: Incremental Analysis                       │");
        println!("└─────────────────────────────────────────────────────┘");

        let analysis_start = Instant::now();
        let analysis = self.analyze_incremental_builds(&graph)?;
        let analysis_time = analysis_start.elapsed().as_millis();

        let modules_to_build = analysis.layers.iter().flatten().count() - analysis.skip_modules.len();
        println!("  ✓ {} modules need rebuilding", modules_to_build);
        println!("  ⚡ {} modules cached (up-to-date)", analysis.skip_modules.len());
        println!("  📊 {} parallel layers", analysis.layers.len());
        println!("  ⏱  {}ms\n", analysis_time);

        println!("┌─────────────────────────────────────────────────────┐");
        println!(
            "│ Phase 3: Parallel Execution ({} workers)              │",
            self.num_workers
        );
        println!("└─────────────────────────────────────────────────────┘");

        let execution_start = Instant::now();
        let build_results = self.execute_builds(analysis.layers, &graph, &analysis.skip_modules)?;
        let execution_time = execution_start.elapsed().as_millis();

        println!("\n  ⏱  {}ms\n", execution_time);

        let mut final_binary_path = None;
        let linking_time = if matches!(manifest.module_type, ManifestModuleType::Binary) {
            println!("┌─────────────────────────────────────────────────────┐");
            println!("│ Phase 4: Linking                                    │");
            println!("└─────────────────────────────────────────────────────┘");

            let linking_start = Instant::now();
            final_binary_path = Some(self.link_binary(manifest, &build_results)?);
            let linking_time = linking_start.elapsed().as_millis();

            println!("  ✓ Executable created: {}", manifest.name);
            println!("  ⏱  {}ms\n", linking_time);
            linking_time
        } else {
            println!("┌─────────────────────────────────────────────────────┐");
            println!("│ Phase 4: Linking (skipped - library)               │");
            println!("└─────────────────────────────────────────────────────┘\n");
            0
        };

        self.update_cache(&build_results, &analysis.module_hashes)?;

        let total_time = build_start.elapsed().as_millis();

        println!("┌═══════════════════════════════════════════════════════┐");
        println!("│ Build Summary                                         │");
        println!("├───────────────────────────────────────────────────────┤");
        println!(
            "│ Total modules:    {:>6}                            │",
            graph.len()
        );
        println!(
            "│ Built:            {:>6}                            │",
            modules_to_build
        );
        println!(
            "│ Cached:           {:>6}                            │",
            analysis.skip_modules.len()
        );
        println!("├───────────────────────────────────────────────────────┤");
        println!(
            "│ Resolution:       {:>6}ms                          │",
            resolution_time
        );
        println!(
            "│ Analysis:         {:>6}ms                          │",
            analysis_time
        );
        println!(
            "│ Execution:        {:>6}ms                          │",
            execution_time
        );
        println!(
            "│ Linking:          {:>6}ms                          │",
            linking_time
        );
        println!("├───────────────────────────────────────────────────────┤");
        println!(
            "│ Total:            {:>6}ms                          │",
            total_time
        );
        println!("└═══════════════════════════════════════════════════════┘\n");

        Ok(BuildStats {
            final_binary_path,
            total_modules: graph.len(),
            modules_built: modules_to_build,
            modules_cached: analysis.skip_modules.len(),
            total_time_ms: total_time,
            resolution_time_ms: resolution_time,
            analysis_time_ms: analysis_time,
            execution_time_ms: execution_time,
            linking_time_ms: linking_time,
        })
    }

    fn resolve_dependencies(&self, manifest: &Manifest) -> BuildResult<DependencyGraph> {
        let mut resolver = DependencyResolver::new(self.root_path.clone());
        resolver.resolve(manifest)
    }

    fn analyze_incremental_builds(
        &self,
        graph: &DependencyGraph,
    ) -> BuildResult<IncrementalBuildAnalysis> {
        let layers = graph.topological_layers()?;

        let mut skip_modules = HashMap::new();
        let mut module_hashes = HashMap::new();
        let mut dependency_hashes: HashMap<String, String> = HashMap::new();

        for layer in &layers {
            for module_name in layer {
                let node = graph
                    .get_node(module_name)
                    .ok_or_else(|| BuildError::Internal(InternalBuildError::BuildNodeNotFound(module_name.to_string())))?;

                let src_path = node.path.join("src");
                let source_hash = HashCalculator::hash_directory(&src_path)
                    .unwrap_or_else(|_| String::from("unknown"));

                let dep_hash_values: Vec<String> = node
                    .dependencies
                    .iter()
                    .filter_map(|dep| dependency_hashes.get(dep).cloned())
                    .collect();
                let dep_hash = HashCalculator::hash_dependencies(&dep_hash_values);

                module_hashes.insert(module_name.clone(), (source_hash.clone(), dep_hash.clone()));

                if self
                    .cache
                    .is_up_to_date(module_name, &source_hash, &dep_hash)
                {
                    skip_modules
                        .insert(module_name.clone(), (source_hash.clone(), dep_hash.clone()));
                }

                dependency_hashes.insert(module_name.clone(), source_hash.clone());
            }
        }

        Ok(IncrementalBuildAnalysis {
            layers,
            skip_modules,
            module_hashes,
        })
    }

    fn execute_builds(
        &self,
        layers: Vec<Vec<String>>,
        graph: &DependencyGraph,
        skip_modules: &HashMap<String, (String, String)>,
    ) -> BuildResult<HashMap<String, BuildResults>> {
        let builder = LayeredBuilder::new(self.num_workers);
        builder.build_layers(layers, graph.nodes(), skip_modules, &self.cache)
    }

    fn link_binary(
        &self,
        manifest: &Manifest,
        build_results: &HashMap<String, BuildResults>,
    ) -> BuildResult<PathBuf> {
        let build_path = self.root_path.join("build");
        let output_executable = build_path.join(&manifest.name);

        let mut all_objects = Vec::new();

        for result in build_results.values() {
            if result.success {
                all_objects.extend(result.object_paths.clone());
            }
        }

        if all_objects.is_empty() {
            return Err(BuildError::Internal(InternalBuildError::NoObjectsToLink));
        }

        link_executable(all_objects, &output_executable)?;

        Ok(output_executable)
    }

    fn update_cache(
        &mut self,
        build_results: &HashMap<String, BuildResults>,
        module_hashes: &HashMap<String, (String, String)>,
    ) -> BuildResult<()> {
        for (module_name, result) in build_results {
            if !result.success {
                continue;
            }

            let (source_hash, dep_hash) = module_hashes.get(module_name).ok_or_else(|| {
                BuildError::Internal(InternalBuildError::ModuleHashNotFound(module_name.clone()))
            })?;

            if let Some(tarball_path) = &result.tarball_path {
                let entry = CacheEntry {
                    source_hash: source_hash.clone(),
                    dependency_hash: dep_hash.clone(),
                    artifact_path: tarball_path.clone(),
                    tarball_path: tarball_path.clone(),
                    object_paths: result.object_paths.clone(),
                    build_timestamp: std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_secs(),
                };

                self.cache.insert(module_name.clone(), entry);
            }
        }

        self.cache.save().map_err(BuildError::FailedToSaveCache)?;

        Ok(())
    }

    #[allow(dead_code)]
    pub fn clean(&mut self) -> BuildResult<()> {
        println!("Cleaning build artifacts...");

        let build_path = self.root_path.join("build");
        if build_path.exists() {
            std::fs::remove_dir_all(&build_path)
                .map_err(BuildError::FailedToCleanBuildArtifacts)?;
        }

        self.cache.clear();
        self.cache.save().map_err(BuildError::FailedToSaveCache)?;

        println!("✓ Build artifacts cleaned");
        Ok(())
    }
}


struct IncrementalBuildAnalysis {
    layers: Vec<Vec<String>>,
    skip_modules: HashMap<String, (String, String)>,
    module_hashes: HashMap<String, (String, String)>,
}
