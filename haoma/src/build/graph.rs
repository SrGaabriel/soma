use std::collections::{HashMap, HashSet, VecDeque};
use std::path::PathBuf;

use crate::build::BuildResult;
use crate::build::errors::BuildError;
use crate::config::manifest::Manifest;

#[derive(Debug, Clone)]
pub struct BuildNode {
    pub name: String,
    pub path: PathBuf,
    pub manifest: Manifest,
    pub dependencies: Vec<String>,
}

#[derive(Debug)]
pub struct DependencyGraph {
    nodes: HashMap<String, BuildNode>,
    adjacency: HashMap<String, Vec<String>>,
}

impl DependencyGraph {
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            adjacency: HashMap::new(),
        }
    }

    pub fn add_node(&mut self, node: BuildNode) {
        let name = node.name.clone();
        let deps = node.dependencies.clone();

        self.nodes.insert(name.clone(), node);
        self.adjacency.insert(name.clone(), deps.clone());
    }

    pub fn get_node(&self, name: &str) -> Option<&BuildNode> {
        self.nodes.get(name)
    }

    pub fn nodes(&self) -> &HashMap<String, BuildNode> {
        &self.nodes
    }

    pub fn validate(&self) -> BuildResult<()> {
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();

        for node_name in self.nodes.keys() {
            if !visited.contains(node_name)
                && self.has_cycle_dfs(node_name, &mut visited, &mut rec_stack)
            {
                return Err(BuildError::CircularDependencyDetected(
                    node_name.clone(),
                ));
            }
        }

        for (node_name, deps) in &self.adjacency {
            for dep in deps {
                if !self.nodes.contains_key(dep) {
                    return Err(BuildError::DependencyNotFound {
                        module: node_name.clone(),
                        missing_dependency: dep.clone(),
                    });
                }
            }
        }

        Ok(())
    }

    fn has_cycle_dfs(
        &self,
        node: &str,
        visited: &mut HashSet<String>,
        rec_stack: &mut HashSet<String>,
    ) -> bool {
        visited.insert(node.to_string());
        rec_stack.insert(node.to_string());

        if let Some(neighbors) = self.adjacency.get(node) {
            for neighbor in neighbors {
                if !visited.contains(neighbor) {
                    if self.has_cycle_dfs(neighbor, visited, rec_stack) {
                        return true;
                    }
                } else if rec_stack.contains(neighbor) {
                    return true;
                }
            }
        }

        rec_stack.remove(node);
        false
    }

    pub fn topological_layers(&self) -> BuildResult<Vec<Vec<String>>> {
        self.validate()?;

        let mut in_degree: HashMap<String, usize> = HashMap::new();
        let adjacency = self.adjacency.clone();

        for node_name in self.nodes.keys() {
            in_degree.insert(node_name.clone(), 0);
        }

        for (node_name, deps) in &adjacency {
            *in_degree.get_mut(node_name).unwrap() = deps.len();
        }

        let mut queue: VecDeque<String> = in_degree
            .iter()
            .filter(|(_, degree)| **degree == 0)
            .map(|(name, _)| name.clone())
            .collect();

        let mut layers = Vec::new();
        let mut processed = 0;

        while !queue.is_empty() {
            let mut current_layer = Vec::new();

            for _ in 0..queue.len() {
                if let Some(node) = queue.pop_front() {
                    current_layer.push(node.clone());
                    processed += 1;

                    for (other_node, other_deps) in &adjacency {
                        if other_deps.contains(&node) {
                            let degree = in_degree.get_mut(other_node).unwrap();
                            *degree -= 1;
                            if *degree == 0 {
                                queue.push_back(other_node.clone());
                            }
                        }
                    }
                }
            }

            if !current_layer.is_empty() {
                layers.push(current_layer);
            }
        }

        if processed != self.nodes.len() {
            return Err(BuildError::GraphIsNotAcyclic);
        }

        Ok(layers)
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }
}
