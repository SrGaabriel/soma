use std::{fs::File, path::Path};

use flate2::read::GzDecoder;
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct BuildTarball {
    pub metadata: BuildMetadata
}

#[derive(Debug, Deserialize)]
pub struct BuildMetadata {
    #[serde(rename = "pmModuleMetadata")]
    pub minimal: MinimalBuildMetadata,
}

#[derive(Debug, Deserialize)]
pub struct MinimalBuildMetadata {
    #[serde(rename = "metaModuleName")]
    pub module_name: String,
    #[serde(rename = "metaVersion")]
    pub version: String,
    #[serde(rename = "metaHash")]
    #[allow(dead_code)]
    pub hash: Option<String>,
}

impl BuildTarball {
    pub fn open(path: &Path) -> std::io::Result<BuildTarball> {
        let file = File::open(path)?;
        let decompressed = GzDecoder::new(file);
        let mut archive = tar::Archive::new(decompressed);
        let metadata = archive
            .entries()?
            .filter_map(Result::ok)
            .find(|entry| {
                entry
                    .path()
                    .ok()
                    .map_or(false, |p| p == Path::new("metadata.json"))
            })
            .ok_or_else(|| {
                std::io::Error::new(std::io::ErrorKind::NotFound, "metadata.json not found")
            })?;

        let metadata: BuildMetadata = serde_json::from_reader(metadata)?;
        Ok(BuildTarball { metadata })
    }
}

