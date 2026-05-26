use std::path::Path;

use crate::{
    build::clean_project,
    logging::output_err,
    style::{self, Tone},
};

pub fn execute(path: &Path) {
    if !path.exists() {
        output_err(format!("path does not exist: `{}`", path.display()));
        std::process::exit(1);
    }
    match clean_project(path) {
        Ok(bytes_removed) => {
            let subject = if bytes_removed == 0 {
                "· nothing to remove".to_string()
            } else {
                format!("· {}", format_bytes(bytes_removed))
            };
            style::status(Tone::Success, "cleaned", subject);
        }
        Err(e) => {
            output_err(format!("clean failed at `{}`: {e}", path.display()));
            std::process::exit(1);
        }
    }
}

#[allow(clippy::cast_precision_loss)]
fn format_bytes(bytes: u64) -> String {
    const KB: f64 = 1024.0;
    const MB: f64 = KB * 1024.0;
    const GB: f64 = MB * 1024.0;
    let b = bytes as f64;
    if b >= GB {
        format!("{:.2} GB", b / GB)
    } else if b >= MB {
        format!("{:.2} MB", b / MB)
    } else if b >= KB {
        format!("{:.2} KB", b / KB)
    } else {
        format!("{bytes} B")
    }
}
