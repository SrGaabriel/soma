use serde::{Deserialize, Serialize};

pub const MANIFEST_NAME: &str = "haoma.toml";

#[derive(Serialize, Deserialize)]
pub struct Manifest {
    pub name: String,
    pub version: String,
    #[serde(default)]
    pub authors: Option<Vec<String>>
}