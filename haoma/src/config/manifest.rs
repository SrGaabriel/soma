use serde::{Deserialize, Serialize};

pub const MANIFEST_NAME: &str = "haoma.toml";

#[derive(Serialize, Deserialize)]
pub struct Manifest {
    pub name: String,
    pub version: String,
    #[serde(default)]
    pub authors: Option<Vec<String>>,
    #[serde(default)]
    pub dependencies: ManifestDependencies
}

#[derive(Serialize, Deserialize, Default)]
pub struct ManifestDependencies {
    #[serde(flatten, skip_serializing_if = "std::collections::HashMap::is_empty", default)]
    pub dependencies: std::collections::HashMap<String, ManifestDependencyValue>
}

impl ManifestDependencies {
    pub fn new() -> Self {
        Self {
            dependencies: std::collections::HashMap::new()
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(untagged)]
pub enum ManifestDependencyValue {
    #[serde(rename = "version")]
    Version(String),
    Custom {
        path: String,
        version: Option<String>
    }
}