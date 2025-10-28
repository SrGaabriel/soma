use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread;

use colored::Colorize;
use indicatif::{MultiProgress, ProgressBar, ProgressStyle};

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
    #[allow(dead_code)]
    pub source_hash: String,
    #[allow(dead_code)]
    pub dependency_hash: String,
    pub error: Option<String>,
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
        _worker_id: usize,
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
                    let result = Self::execute_build(work_item);

                    if result_sender.send(result).is_err() {
                        break;
                    }
                }
                Ok(WorkerMessage::Shutdown) => {
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

        let dep_hash_values: Vec<String> = work_item
            .dependency_tarballs
            .keys()
            .map(|_| source_hash.clone())
            .collect();
        let dependency_hash = HashCalculator::hash_dependencies(&dep_hash_values);

        match compile_module(&node, &work_item.dependency_tarballs) {
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
        layers: Vec<Vec<String>>,
        nodes: &HashMap<String, BuildNode>,
        skip_modules: &HashMap<String, (String, String)>,
        cache: &BuildCache,
        multi_progress: &MultiProgress,
    ) -> BuildResult<HashMap<String, BuildResults>> {
        let mut results = HashMap::new();
        let mut tarball_paths: HashMap<String, PathBuf> = HashMap::new();

        for (layer_idx, layer) in layers.iter().enumerate() {
            let layer_pb = multi_progress.add(ProgressBar::new(layer.len() as u64));
            layer_pb.set_style(
                ProgressStyle::default_bar()
                    .template("{spinner:.green} [{bar:40.cyan/blue}] {pos}/{len} {msg}")
                    .unwrap()
                    .progress_chars("█▓▒░  "),
            );
            layer_pb.set_message(format!("Layer {}", layer_idx + 1));

            let mut pending = layer.len();
            let mut layer_failed = false;

            for module_name in layer {
                if let Some((source_hash, dep_hash)) = skip_modules.get(module_name) {
                    layer_pb.set_message(format!(
                        "Layer {} | {} {}",
                        layer_idx + 1,
                        "⚡".yellow(),
                        module_name.dimmed()
                    ));

                    if let Some(cache_entry) = cache.get(module_name) {
                        tarball_paths.insert(module_name.clone(), cache_entry.tarball_path.clone());
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

                    layer_pb.inc(1);
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

                let mut dependency_tarballs = HashMap::new();
                for dep_name in &node.dependencies {
                    if let Some(dep_tarball) = tarball_paths.get(dep_name) {
                        dependency_tarballs.insert(dep_name.clone(), dep_tarball.clone());
                    }
                }

                self.scheduler.submit(node, dependency_tarballs)?;
            }

            while pending > 0 {
                if let Some(result) = self.scheduler.receive_result() {
                    pending -= 1;

                    if result.success {
                        layer_pb.set_message(format!(
                            "Layer {} | {} {}",
                            layer_idx + 1,
                            "✓".green(),
                            result.module_name
                        ));
                        if let Some(tarball) = &result.tarball_path {
                            tarball_paths.insert(result.module_name.clone(), tarball.clone());
                        }
                    } else {
                        layer_pb.set_message(format!(
                            "Layer {} | {} {}",
                            layer_idx + 1,
                            "✗".red(),
                            result.module_name
                        ));
                        if let Some(error) = &result.error {
                            layer_pb.println(format!("    Error: {}", error));
                        }
                        layer_failed = true;
                    }

                    layer_pb.inc(1);
                    results.insert(result.module_name.clone(), result);
                } else {
                    return Err(BuildError::Internal(
                        crate::build::errors::InternalBuildError::FailedToReceiveBuildResult,
                    ));
                }
            }

            layer_pb.finish_with_message(format!(
                "Layer {} {} {}",
                layer_idx + 1,
                "✓".green(),
                "complete".dimmed()
            ));

            if layer_failed {
                layer_pb.finish_with_message(format!(
                    "Layer {} {} {}",
                    layer_idx + 1,
                    "✗".red(),
                    "failed".red()
                ));
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
