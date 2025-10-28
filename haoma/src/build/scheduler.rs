use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread;

use crate::build::BuildResult;
use crate::build::cache::{BuildCache, HashCalculator};
use crate::build::compile::compile_module;
use crate::build::errors::{BuildError, InternalBuildError};
use crate::build::graph::BuildNode;

#[derive(Debug, Clone)]
pub struct BuildResults {
    pub module_name: String,
    pub success: bool,
    pub tarball_path: Option<PathBuf>,
    pub object_paths: Vec<PathBuf>,
    pub source_hash: String,
    #[allow(dead_code)]
    pub dependency_hash: String,
    pub error: Option<String>,
}

#[derive(Debug, Clone)]
struct WorkItem {
    node: BuildNode,
    dependency_hashes: HashMap<String, String>,
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
                Self::worker_loop(worker_id, work_receiver, result_sender);
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
        worker_id: usize,
        work_receiver: Arc<Mutex<Receiver<WorkerMessage>>>,
        result_sender: Sender<BuildResults>,
    ) {
        loop {
            let message = {
                let receiver = work_receiver.lock().unwrap();
                receiver.recv()
            };

            match message {
                Ok(WorkerMessage::Build(work_item)) => {
                    println!(
                        "[Worker {}] Building module '{}'",
                        worker_id, work_item.node.name
                    );

                    let result = Self::execute_build(work_item);

                    if result_sender.send(result).is_err() {
                        eprintln!("[Worker {}] Failed to send result", worker_id);
                        break;
                    }
                }
                Ok(WorkerMessage::Shutdown) => {
                    println!("[Worker {}] Shutting down", worker_id);
                    break;
                }
                Err(_) => {
                    break;
                }
            }
        }
    }

    fn execute_build(work_item: Box<WorkItem>) -> BuildResults {
        let node = work_item.node;
        let module_name = node.name.clone();

        let src_path = node.path.join("src");
        let source_hash =
            HashCalculator::hash_directory(&src_path).unwrap_or_else(|_| String::from("unknown"));

        let dep_hash_values: Vec<String> = work_item.dependency_hashes.values().cloned().collect();
        let dependency_hash = HashCalculator::hash_dependencies(&dep_hash_values);

        match compile_module(&node, &work_item.dependency_hashes) {
            Ok((tarball, objects)) => BuildResults {
                module_name,
                success: true,
                tarball_path: Some(tarball),
                object_paths: objects,
                source_hash,
                dependency_hash,
                error: None,
            },
            Err(e) => BuildResults {
                module_name,
                success: false,
                tarball_path: None,
                object_paths: Vec::new(),
                source_hash,
                dependency_hash,
                error: Some(e),
            },
        }
    }

    pub fn submit(
        &self,
        node: BuildNode,
        dependency_hashes: HashMap<String, String>,
    ) -> BuildResult<()> {
        let node_name = node.name.clone();
        let work_item = WorkItem {
            node,
            dependency_hashes,
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
        layers: Vec<Vec<String>>,
        nodes: &HashMap<String, BuildNode>,
        skip_modules: &HashMap<String, (String, String)>,
        cache: &BuildCache,
    ) -> BuildResult<HashMap<String, BuildResults>> {
        let mut results = HashMap::new();
        let mut hashes: HashMap<String, String> = HashMap::new();

        for (layer_idx, layer) in layers.iter().enumerate() {
            println!(
                "\n=== Building Layer {} ({} modules) ===",
                layer_idx + 1,
                layer.len()
            );

            let mut pending = layer.len();
            let mut layer_failed = false;

            for module_name in layer {
                if let Some((source_hash, dep_hash)) = skip_modules.get(module_name) {
                    println!("  ⚡ Skipping '{}' (up-to-date)", module_name);
                    hashes.insert(module_name.clone(), source_hash.clone());

                    if let Some(cache_entry) = cache.get(module_name) {
                        let cached_result = BuildResults {
                            module_name: module_name.clone(),
                            success: true,
                            tarball_path: Some(cache_entry.tarball_path.clone()),
                            object_paths: cache_entry.object_paths.clone(),
                            source_hash: source_hash.clone(),
                            dependency_hash: dep_hash.clone(),
                            error: None,
                        };
                        results.insert(module_name.clone(), cached_result);
                    }

                    pending -= 1;
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

                let mut dependency_hashes = HashMap::new();
                for dep_name in &node.dependencies {
                    if let Some(dep_hash) = hashes.get(dep_name) {
                        dependency_hashes.insert(dep_name.clone(), dep_hash.clone());
                    }
                }

                self.scheduler.submit(node, dependency_hashes)?;
            }

            while pending > 0 {
                if let Some(result) = self.scheduler.receive_result() {
                    pending -= 1;

                    if result.success {
                        println!("  ✓ Built '{}'", result.module_name);
                        hashes.insert(result.module_name.clone(), result.source_hash.clone());
                    } else {
                        println!("  ✗ Failed to build '{}'", result.module_name);
                        if let Some(error) = &result.error {
                            eprintln!("    Error: {}", error);
                        }
                        layer_failed = true;
                    }

                    results.insert(result.module_name.clone(), result);
                } else {
                    return Err(BuildError::Internal(
                        crate::build::errors::InternalBuildError::FailedToReceiveBuildResult,
                    ));
                }
            }

            if layer_failed {
                self.scheduler.shutdown();
                return Err(BuildError::Internal(
                    InternalBuildError::UnexpectedLayerBuildFailure(layer_idx + 1),
                ));
            }
        }

        self.scheduler.shutdown();
        Ok(results)
    }
}
