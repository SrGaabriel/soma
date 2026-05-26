use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread;

use crate::build::BuildResult;
use crate::build::cache::{BuildCache, HashCalculator};
use crate::build::compile::{compile_binary, compile_lib};
use crate::build::consts::SRC_FOLDER_NAME;
use crate::build::errors::{BuildError, InternalBuildError};
use crate::build::graph::BuildNode;
use crate::build::progress::ProgressDisplay;
use crate::config::manifest::ManifestModuleType;
use crate::style::{self, Tone};

#[derive(Debug)]
pub struct BuildResults {
    pub module_name: String,
    pub success: bool,
    pub output_path: Option<PathBuf>,
    #[allow(dead_code)]
    pub source_hash: String,
    #[allow(dead_code)]
    pub dependency_hash: String,
    pub error: Option<BuildError>,
}

#[derive(Debug, Clone)]
struct WorkItem {
    node: BuildNode,
    dependency_tarballs: HashMap<String, PathBuf>,
}

enum WorkerMessage {
    Build(Box<WorkItem>),
    Shutdown,
}

pub struct BuildScheduler {
    num_workers: usize,
    workers: Vec<thread::JoinHandle<()>>,
    work_sender: Sender<WorkerMessage>,
    result_receiver: Receiver<BuildResults>,
}

impl BuildScheduler {
    pub fn new(num_workers: usize) -> Self {
        let (work_sender, work_receiver) = mpsc::channel::<WorkerMessage>();
        let (result_sender, result_receiver) = mpsc::channel::<BuildResults>();

        let work_receiver = Arc::new(Mutex::new(work_receiver));
        let mut workers = Vec::new();

        for worker_id in 0..num_workers {
            let work_receiver = Arc::clone(&work_receiver);
            let result_sender = result_sender.clone();

            let handle = thread::spawn(move || {
                Self::worker_loop(worker_id, &work_receiver, &result_sender);
            });

            workers.push(handle);
        }

        Self {
            num_workers,
            workers,
            work_sender,
            result_receiver,
        }
    }

    fn worker_loop(
        _worker_id: usize,
        work_receiver: &Mutex<Receiver<WorkerMessage>>,
        result_sender: &Sender<BuildResults>,
    ) {
        loop {
            let message = {
                let receiver = work_receiver.lock().unwrap();
                receiver.recv()
            };

            match message {
                Ok(WorkerMessage::Build(work_item)) => {
                    let result = Self::execute_build(work_item);

                    if result_sender.send(result).is_err() {
                        break;
                    }
                }
                Ok(WorkerMessage::Shutdown) | Err(_) => {
                    break;
                }
            }
        }
    }

    fn execute_build(work_item: Box<WorkItem>) -> BuildResults {
        let node = work_item.node;
        let module_name = node.name.clone();

        let src_path = node.path.join(SRC_FOLDER_NAME);
        let source_hash =
            HashCalculator::hash_directory(&src_path).unwrap_or_else(|_| String::from("unknown"));

        let dep_hash_values: Vec<String> = work_item
            .dependency_tarballs
            .keys()
            .map(|_| source_hash.clone())
            .collect();
        let dependency_hash = HashCalculator::hash_dependencies(&dep_hash_values);
        let compilation_result = match node.manifest.module_type {
            ManifestModuleType::Binary => compile_binary(&node, &work_item.dependency_tarballs),
            ManifestModuleType::Library => compile_lib(&node, &work_item.dependency_tarballs),
        };

        match compilation_result {
            Ok(compilation_output) => BuildResults {
                module_name,
                success: true,
                output_path: Some(compilation_output),
                source_hash,
                dependency_hash,
                error: None,
            },
            Err(e) => BuildResults {
                module_name,
                success: false,
                output_path: None,
                source_hash,
                dependency_hash,
                error: Some(e),
            },
        }
    }

    pub fn submit(
        &self,
        node: BuildNode,
        dependency_tarballs: HashMap<String, PathBuf>,
    ) -> BuildResult<()> {
        let node_name = node.name.clone();
        let work_item = WorkItem {
            node,
            dependency_tarballs,
        };

        self.work_sender
            .send(WorkerMessage::Build(Box::new(work_item)))
            .map_err(|_| {
                BuildError::Internal(InternalBuildError::UnexpectedSchedulerReceiverShutdown(
                    node_name,
                ))
            })
    }

    pub fn receive_result(&self) -> Option<BuildResults> {
        self.result_receiver.recv().ok()
    }

    pub fn shutdown(self) {
        for _ in 0..self.num_workers {
            let _ = self.work_sender.send(WorkerMessage::Shutdown);
        }

        for handle in self.workers {
            let _ = handle.join();
        }
    }
}

pub struct LayeredBuilder {
    scheduler: BuildScheduler,
}

impl LayeredBuilder {
    pub fn new(num_workers: usize) -> Self {
        Self {
            scheduler: BuildScheduler::new(num_workers),
        }
    }

    pub fn build_layers(
        self,
        layers: &[Vec<String>],
        nodes: &HashMap<String, BuildNode>,
        skip_modules: &HashMap<String, (String, String)>,
        cache: &BuildCache,
    ) -> BuildResult<HashMap<String, BuildResults>> {
        let total_to_build: usize = layers
            .iter()
            .map(|l| l.iter().filter(|m| !skip_modules.contains_key(*m)).count())
            .sum();

        let mut display = ProgressDisplay::new(total_to_build);
        let mut results = HashMap::new();
        let mut tarball_paths: HashMap<String, PathBuf> = HashMap::new();

        for (layer_idx, layer) in layers.iter().enumerate() {
            let mut pending = 0usize;
            let mut layer_failed = false;

            for module_name in layer {
                if let Some((source_hash, dep_hash)) = skip_modules.get(module_name) {
                    if let Some(cache_entry) = cache.get(module_name) {
                        tarball_paths.insert(module_name.clone(), cache_entry.tarball_path.clone());
                        results.insert(
                            module_name.clone(),
                            BuildResults {
                                module_name: module_name.clone(),
                                success: true,
                                output_path: Some(cache_entry.tarball_path.clone()),
                                source_hash: source_hash.clone(),
                                dependency_hash: dep_hash.clone(),
                                error: None,
                            },
                        );
                    }
                    if style::is_verbose() {
                        display.print_above(&style::format_status(
                            Tone::Note,
                            "cached",
                            module_name,
                        ));
                    }
                    continue;
                }

                let node = nodes
                    .get(module_name)
                    .ok_or_else(|| {
                        BuildError::Internal(InternalBuildError::BuildNodeNotFound(
                            module_name.clone(),
                        ))
                    })?
                    .clone();

                let mut dependency_tarballs = HashMap::new();
                let mut to_visit: Vec<String> = node.dependencies.clone();
                let mut visited: std::collections::HashSet<String> =
                    std::collections::HashSet::new();

                while let Some(dep_name) = to_visit.pop() {
                    if visited.contains(&dep_name) {
                        continue;
                    }
                    visited.insert(dep_name.clone());

                    if let Some(dep_tarball) = tarball_paths.get(&dep_name) {
                        dependency_tarballs.insert(dep_name.clone(), dep_tarball.clone());
                    }

                    if let Some(dep_node) = nodes.get(&dep_name) {
                        for transitive_dep in &dep_node.dependencies {
                            if !visited.contains(transitive_dep) {
                                to_visit.push(transitive_dep.clone());
                            }
                        }
                    }
                }

                display.start(module_name, &node.manifest.version);
                self.scheduler.submit(node, dependency_tarballs)?;
                pending += 1;
            }

            while pending > 0 {
                let Some(result) = self.scheduler.receive_result() else {
                    return Err(BuildError::Internal(
                        crate::build::errors::InternalBuildError::FailedToReceiveBuildResult,
                    ));
                };
                pending -= 1;

                display.finish(&result.module_name);

                if result.success {
                    if let Some(tarball) = &result.output_path {
                        tarball_paths.insert(result.module_name.clone(), tarball.clone());
                    }
                    if style::is_verbose() {
                        display.print_above(&style::format_status(
                            Tone::Progress,
                            "compiled",
                            &result.module_name,
                        ));
                    }
                } else {
                    if let Some(error) = &result.error {
                        display.print_above(&style::format_status(
                            Tone::Error,
                            "error",
                            format!("{}: {error}", result.module_name),
                        ));
                    }
                    layer_failed = true;
                }

                results.insert(result.module_name.clone(), result);
            }

            if layer_failed {
                display.finish_all();
                self.scheduler.shutdown();
                return Err(BuildError::Internal(
                    InternalBuildError::UnexpectedLayerBuildFailure(layer_idx + 1),
                ));
            }
        }

        display.finish_all();
        self.scheduler.shutdown();
        Ok(results)
    }
}
