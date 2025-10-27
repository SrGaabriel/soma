use std::{fs::File, path::Path};

use flate2::read::GzDecoder;
use serde::Deserialize;

pub struct BuildTarball {
    pub metadata: BuildMetadata,
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
    pub fn open(path: &Path, unpack_to: Option<&Path>) -> std::io::Result<BuildTarball> {
        let file = File::open(path)?;
        let decompressed = GzDecoder::new(file);
        let mut archive = tar::Archive::new(decompressed);

        let mut metadata = None;
        println!("Decoding: {}", path.display());

        for entry in archive.entries()? {
            println!("Entry: {:?}", entry.as_ref().map(|e| e.path()));
            let mut entry = entry?;
            println!("b");
            let entry_path = {
                let p = entry.path()?;
                p.as_ref().to_path_buf()
            };
            println!("c: {:?}", entry_path);

            if entry_path == Path::new("metadata.json") {
                metadata = Some(serde_json::from_reader(&mut entry)?);
            } else if let Some(unpack_to) = unpack_to {
                println!("Unpacking object: {:?}", entry_path);
                if let Some(parent) = path.parent() {
                    std::fs::create_dir_all(parent)?;
                }
                entry.unpack_in(unpack_to)?;
            }
        }

        let metadata = metadata.ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::NotFound, "metadata.json not found")
        })?;

        Ok(BuildTarball { metadata })
    }
}
