use std::collections::HashMap;
use std::fs;
use std::path::Path;

use kdl::KdlError;

use crate::core::{Result, Semver, SvmError, Version};

#[derive(Debug, Clone)]
pub struct Toolchain {
    pub version: Version,
    pub components: HashMap<String, Version>,
    pub compatibility: HashMap<String, VersionRequirement>,
}

#[derive(Debug, Clone)]
pub struct VersionRequirement {
    pub min: Option<Semver>,
    pub max: Option<Semver>,
}

impl VersionRequirement {
    pub fn satisfies(&self, version: &Version) -> bool {
        match version {
            Version::Dev => true, // dev always satisfies
            Version::Semver(v) => {
                if let Some(ref min) = self.min
                    && v < min
                {
                    return false;
                }
                if let Some(ref max) = self.max
                    && v > max
                {
                    return false;
                }
                true
            }
        }
    }
}

impl Toolchain {
    pub fn load(project_root: &Path) -> Result<Option<Self>> {
        let path = project_root.join("soma-toolchain.kdl");
        if !path.exists() {
            return Ok(None);
        }

        let content =
            fs::read_to_string(&path).map_err(|e: std::io::Error| SvmError::io(&path, e))?;
        let doc: kdl::KdlDocument = content
            .parse()
            .map_err(|e: KdlError| SvmError::InvalidToolchain(format!("{}", e)))?;

        let mut version = Version::Dev;
        let mut components = HashMap::new();
        let mut compatibility = HashMap::new();

        if let Some(toolchain_node) = doc.get("toolchain")
            && let Some(children) = toolchain_node.children()
            && let Some(ver_node) = children.get("version")
            && let Some(entry) = ver_node.entries().first()
            && let Some(v) = entry.value().as_string()
        {
            version = v
                .parse()
                .map_err(|e: String| SvmError::InvalidToolchain(e.to_string()))?;
        }

        if let Some(comp_node) = doc.get("components")
            && let Some(children) = comp_node.children()
        {
            for node in children.nodes() {
                let name = node.name().value().to_string();
                if let Some(entry) = node.entries().first()
                    && let Some(v) = entry.value().as_string()
                {
                    let comp_version: Version = v
                        .parse()
                        .map_err(|e: String| SvmError::InvalidToolchain(e.to_string()))?;
                    components.insert(name, comp_version);
                }
            }
        }

        if let Some(compat_node) = doc.get("compatibility")
            && let Some(children) = compat_node.children()
        {
            for node in children.nodes() {
                let name = node.name().value().to_string();
                let mut req = VersionRequirement {
                    min: None,
                    max: None,
                };

                if let Some(node_children) = node.children() {
                    if let Some(min_node) = node_children.get("min")
                        && let Some(entry) = min_node.entries().first()
                        && let Some(v) = entry.value().as_string()
                    {
                        req.min = Some(
                            v.parse()
                                .map_err(|e: String| SvmError::InvalidToolchain(e.to_string()))?,
                        );
                    }
                    if let Some(max_node) = node_children.get("max")
                        && let Some(entry) = max_node.entries().first()
                        && let Some(v) = entry.value().as_string()
                    {
                        req.max = Some(
                            v.parse()
                                .map_err(|e: String| SvmError::InvalidToolchain(e.to_string()))?,
                        );
                    }
                }

                compatibility.insert(name, req);
            }
        }

        Ok(Some(Self {
            version,
            components,
            compatibility,
        }))
    }

    pub fn version_for(&self, component: &str) -> &Version {
        self.components.get(component).unwrap_or(&self.version)
    }

    pub fn check_compatibility(&self, component: &str, version: &Version) -> Result<()> {
        if let Some(req) = self.compatibility.get(component)
            && !req.satisfies(version)
        {
            return Err(SvmError::IncompatibleVersions(format!(
                "{} {} does not satisfy requirements",
                component, version
            )));
        }
        Ok(())
    }
}
