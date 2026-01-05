use std::fs;
use std::path::{Path, PathBuf};

use directories::BaseDirs;

use crate::core::{Result, SvmError, Target, Version};

pub struct SvmDirs {
    root: PathBuf,
}

impl SvmDirs {
    pub fn new() -> Result<Self> {
        let base_dirs = BaseDirs::new().ok_or_else(|| SvmError::Io {
            path: PathBuf::from("~"),
            source: std::io::Error::new(std::io::ErrorKind::NotFound, "Home directory not found"),
        })?;
        Ok(Self {
            root: base_dirs.home_dir().join(".svm"),
        })
    }

    pub fn with_root(root: PathBuf) -> Self {
        Self { root }
    }

    pub fn ensure_dirs(&self) -> Result<()> {
        let dirs = [
            self.root.clone(),
            self.versions_dir(),
            self.cache_dir(),
            self.current_dir(),
        ];

        for dir in dirs {
            fs::create_dir_all(&dir).map_err(|e| SvmError::io(&dir, e))?;
        }

        Ok(())
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn versions_dir(&self) -> PathBuf {
        self.root.join("versions")
    }

    pub fn version_dir(&self, version: &Version) -> PathBuf {
        self.versions_dir().join(version.to_string())
    }

    pub fn bin_dir(&self, version: &Version, target: &Target) -> PathBuf {
        self.version_dir(version).join(target.to_string())
    }

    pub fn current_dir(&self) -> PathBuf {
        self.root.join("current")
    }

    pub fn current_bin_dir(&self, target: &Target) -> PathBuf {
        self.current_dir().join(target.to_string())
    }

    pub fn cache_dir(&self) -> PathBuf {
        self.root.join("cache")
    }

    pub fn config_file(&self) -> PathBuf {
        self.root.join("config.kdl")
    }

    pub fn is_installed(&self, version: &Version, target: &Target) -> bool {
        self.bin_dir(version, target).exists()
    }

    pub fn installed_versions(&self) -> Result<Vec<Version>> {
        let versions_dir = self.versions_dir();
        if !versions_dir.exists() {
            return Ok(Vec::new());
        }

        let mut versions = Vec::new();
        let entries = fs::read_dir(&versions_dir).map_err(|e| SvmError::io(&versions_dir, e))?;

        for entry in entries {
            let entry = entry.map_err(|e| SvmError::io(&versions_dir, e))?;
            let name = entry.file_name();
            if let Some(name_str) = name.to_str()
                && let Ok(version) = name_str.parse()
            {
                versions.push(version);
            }
        }

        Ok(versions)
    }

    pub fn current_version(&self, target: &Target) -> Result<Option<Version>> {
        let link = self.current_bin_dir(target);
        if !link.exists() {
            return Ok(None);
        }

        let target_path = fs::read_link(&link).map_err(|e| SvmError::io(&link, e))?;

        let components: Vec<_> = target_path.components().collect();
        for (i, comp) in components.iter().enumerate() {
            if let std::path::Component::Normal(s) = comp
                && s.to_str() == Some("versions")
                && let Some(std::path::Component::Normal(version_str)) = components.get(i + 1)
                && let Some(v) = version_str.to_str()
                && let Ok(version) = v.parse()
            {
                return Ok(Some(version));
            }
        }

        Ok(None)
    }

    pub fn set_current(&self, version: &Version, target: &Target) -> Result<()> {
        let link = self.current_bin_dir(target);
        let target_dir = self.bin_dir(version, target);

        if !target_dir.exists() {
            return Err(SvmError::VersionNotInstalled(version.to_string()));
        }

        if link.exists() || link.is_symlink() {
            fs::remove_file(&link).map_err(|e| SvmError::io(&link, e))?;
        }

        if let Some(parent) = link.parent() {
            fs::create_dir_all(parent).map_err(|e| SvmError::io(parent, e))?;
        }

        #[cfg(unix)]
        std::os::unix::fs::symlink(&target_dir, &link).map_err(|e| SvmError::io(&link, e))?;

        #[cfg(windows)]
        std::os::windows::fs::symlink_dir(&target_dir, &link)
            .map_err(|e| SvmError::io(&link, e))?;

        Ok(())
    }

    pub fn remove_version(&self, version: &Version) -> Result<()> {
        let dir = self.version_dir(version);
        if !dir.exists() {
            return Err(SvmError::VersionNotInstalled(version.to_string()));
        }
        fs::remove_dir_all(&dir).map_err(|e| SvmError::io(&dir, e))?;
        Ok(())
    }
}

impl Default for SvmDirs {
    fn default() -> Self {
        Self::new().expect("Failed to initialize SVM directories")
    }
}

pub fn find_project_root() -> Option<PathBuf> {
    let current = std::env::current_dir().ok()?;

    for ancestor in current.ancestors() {
        if ancestor.join("soma.kdl").exists()
            || (ancestor.join("compiler").exists() && ancestor.join("haoma").exists())
        {
            return Some(ancestor.to_path_buf());
        }
    }

    None
}
