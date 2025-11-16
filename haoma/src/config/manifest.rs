use serde::{Deserialize, Serialize};

pub const MANIFEST_NAME: &str = "haoma.toml";

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Manifest {
    pub name: String,
    pub version: String,
    #[serde(rename = "type")]
    pub module_type: ManifestModuleType,
    #[serde(default)]
    pub authors: Option<Vec<String>>,
    #[serde(default)]
    pub dependencies: ManifestDependencies,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub enum ManifestModuleType {
    #[serde(rename = "library")]
    Library,
    #[serde(rename = "binary")]
    Binary,
}

#[derive(Serialize, Deserialize, Default, Debug, Clone)]
pub struct ManifestDependencies {
    #[serde(
        flatten,
        skip_serializing_if = "std::collections::HashMap::is_empty",
        default
    )]
    pub dependencies: std::collections::HashMap<String, ManifestDependencyValue>,
}

impl ManifestDependencies {
    pub fn new() -> Self {
        Self {
            dependencies: std::collections::HashMap::new(),
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(untagged)]
pub enum ManifestDependencyValue {
    #[serde(rename = "version")]
    Version(String),
    Custom {
        path: String,
        version: Option<String>,
    },
}
