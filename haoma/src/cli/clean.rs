use std::path::Path;

use crate::{
    build::clean_project,
    logging::{output_err, output_ok},
};

pub fn execute(path: &Path) {
    if !path.exists() {
        output_err(&format!(
            "The specified path does not exist: {}",
            path.display()
        ));
    }
    let clearing_result = clean_project(path);
    if let Err(e) = clearing_result {
        output_err(&format!(
            "An error occurred while cleaning the project at {}: {}",
            path.display(),
            e
        ));
    }
    output_ok("Project cleaned successfully.");
}
