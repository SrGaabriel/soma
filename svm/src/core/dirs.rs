use std::fs;
use std::path::PathBuf;

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

    pub fn versions_dir(&self) -> PathBuf {
        self.root.join("versions")
    }

    pub fn version_dir(&self, version: &Version) -> PathBuf {
        self.versions_dir().join(version.to_string())
    }

    pub fn bin_dir(&self, version: &Version, target: &Target) -> PathBuf {
        self.version_dir(version)
            .join(target.to_string())
            .join("bin")
    }

    pub fn lib_dir(&self, version: &Version, target: &Target) -> PathBuf {
        self.version_dir(version)
            .join(target.to_string())
            .join("lib")
    }

    pub fn current_dir(&self) -> PathBuf {
        self.root.join("current")
    }

    pub fn current_bin_dir(&self, target: &Target) -> PathBuf {
        self.current_dir().join(target.to_string()).join("bin")
    }

    pub fn current_lib_dir(&self, target: &Target) -> PathBuf {
        self.current_dir().join(target.to_string()).join("lib")
    }

    pub fn cache_dir(&self) -> PathBuf {
        self.root.join("cache")
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
        let bin_link = self.current_bin_dir(target);
        let bin_target = self.bin_dir(version, target);

        if !bin_target.exists() {
            return Err(SvmError::VersionNotInstalled(version.to_string()));
        }

        if bin_link.is_symlink() {
            fs::remove_file(&bin_link).map_err(|e| SvmError::io(&bin_link, e))?;
        } else if bin_link.is_dir() {
            fs::remove_dir_all(&bin_link).map_err(|e| SvmError::io(&bin_link, e))?;
        } else if bin_link.exists() {
            fs::remove_file(&bin_link).map_err(|e| SvmError::io(&bin_link, e))?;
        }

        if let Some(parent) = bin_link.parent() {
            fs::create_dir_all(parent).map_err(|e| SvmError::io(parent, e))?;
        }

        #[cfg(unix)]
        std::os::unix::fs::symlink(&bin_target, &bin_link)
            .map_err(|e| SvmError::io(&bin_link, e))?;

        #[cfg(windows)]
        std::os::windows::fs::symlink_dir(&bin_target, &bin_link)
            .map_err(|e| SvmError::io(&bin_link, e))?;

        // Symlink lib directory
        let lib_link = self.current_lib_dir(target);
        let lib_target = self.lib_dir(version, target);

        if lib_target.exists() {
            if lib_link.is_symlink() {
                fs::remove_file(&lib_link).map_err(|e| SvmError::io(&lib_link, e))?;
            } else if lib_link.is_dir() {
                fs::remove_dir_all(&lib_link).map_err(|e| SvmError::io(&lib_link, e))?;
            } else if lib_link.exists() {
                fs::remove_file(&lib_link).map_err(|e| SvmError::io(&lib_link, e))?;
            }

            if let Some(parent) = lib_link.parent() {
                fs::create_dir_all(parent).map_err(|e| SvmError::io(parent, e))?;
            }

            #[cfg(unix)]
            std::os::unix::fs::symlink(&lib_target, &lib_link)
                .map_err(|e| SvmError::io(&lib_link, e))?;

            #[cfg(windows)]
            std::os::windows::fs::symlink_dir(&lib_target, &lib_link)
                .map_err(|e| SvmError::io(&lib_link, e))?;
        }

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
