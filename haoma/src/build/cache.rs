use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use crate::build::BuildResult;
use crate::build::errors::BuildError;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheEntry {
    pub source_hash: String,
    pub dependency_hash: String,
    pub artifact_path: PathBuf,
    pub tarball_path: PathBuf,
    pub build_timestamp: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct BuildCache {
    entries: HashMap<String, CacheEntry>,
    cache_path: PathBuf,
}

impl BuildCache {
    pub fn load(cache_dir: &Path) -> BuildResult<Self> {
        let cache_path = cache_dir.join("build_cache.json");

        if cache_path.exists() {
            let mut file = File::open(&cache_path).map_err(BuildError::UnavailableBuildCache)?;
            let mut contents = String::new();
            file.read_to_string(&mut contents)
                .map_err(BuildError::UnavailableBuildCache)?;

            let entries: HashMap<String, CacheEntry> =
                serde_json::from_str(&contents).unwrap_or_else(|_| HashMap::new());

            Ok(Self {
                entries,
                cache_path,
            })
        } else {
            Ok(Self {
                entries: HashMap::new(),
                cache_path,
            })
        }
    }

    pub fn save(&self) -> io::Result<()> {
        if let Some(parent) = self.cache_path.parent() {
            fs::create_dir_all(parent)?;
        }

        let contents = serde_json::to_string_pretty(&self.entries)?;
        let mut file = File::create(&self.cache_path)?;
        file.write_all(contents.as_bytes())?;
        Ok(())
    }

    pub fn is_up_to_date(
        &self,
        module_name: &str,
        source_hash: &str,
        dependency_hash: &str,
    ) -> bool {
        if let Some(entry) = self.entries.get(module_name) {
            if entry.source_hash != source_hash || entry.dependency_hash != dependency_hash {
                return false;
            }

            if !entry.tarball_path.exists() {
                return false;
            }

            true
        } else {
            false
        }
    }

    pub fn get(&self, module_name: &str) -> Option<&CacheEntry> {
        self.entries.get(module_name)
    }

    pub fn insert(&mut self, module_name: String, entry: CacheEntry) {
        self.entries.insert(module_name, entry);
    }

    #[allow(dead_code)]
    pub fn remove(&mut self, module_name: &str) {
        self.entries.remove(module_name);
    }

    pub fn clear(&mut self) {
        self.entries.clear();
    }
}

pub struct HashCalculator;

impl HashCalculator {
    pub fn hash_directory(path: &Path) -> io::Result<String> {
        let mut hasher = Sha256::new();
        let mut files = Vec::new();

        Self::collect_files(path, &mut files)?;

        files.sort();

        for file_path in files {
            let relative = file_path.strip_prefix(path).unwrap_or(&file_path);
            hasher.update(relative.to_string_lossy().as_bytes());

            let contents = fs::read(&file_path)?;
            hasher.update(&contents);
        }

        Ok(format!("{:x}", hasher.finalize()))
    }

    pub fn hash_dependencies(dep_hashes: &[String]) -> String {
        let mut hasher = Sha256::new();
        let mut sorted = dep_hashes.to_vec();
        sorted.sort();

        for hash in sorted {
            hasher.update(hash.as_bytes());
        }

        format!("{:x}", hasher.finalize())
    }

    fn collect_files(dir: &Path, files: &mut Vec<PathBuf>) -> io::Result<()> {
        if dir.is_dir() {
            for entry in fs::read_dir(dir)? {
                let entry = entry?;
                let path = entry.path();

                if path.is_dir() {
                    Self::collect_files(&path, files)?;
                } else {
                    files.push(path);
                }
            }
        }
        Ok(())
    }
}
