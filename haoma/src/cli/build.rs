use std::path::Path;

use crate::{
    build::{BuildStats, build_project},
    cli::parse_manifest,
    logging::{output_debug, output_err},
    style::{self, Hyperlink, Tone},
};

pub fn execute(path: &Path, profile: &str) {
    let manifest = parse_manifest(path);
    output_debug("Successfully read manifest file");
    match build_project(path, &manifest) {
        Ok(build) => {
            print_build_summary(&build, profile);
        }
        Err(e) => {
            output_err(format!("build failed: {e}"));
            std::process::exit(1);
        }
    }
}

pub fn print_build_summary(stats: &BuildStats, profile: &str) {
    let count = if stats.modules_built == 0 {
        format!("{} cached", stats.modules_cached)
    } else if stats.modules_cached > 0 {
        format!(
            "{} built, {} cached",
            stats.modules_built, stats.modules_cached
        )
    } else {
        format!("{} built", stats.modules_built)
    };

    style::status(
        Tone::Success,
        "done",
        format!(
            "· {profile} · {count} · {}",
            format_duration(stats.total_time_ms)
        ),
    );

    if let Some(binary_path) = &stats.final_binary_path {
        let link = Hyperlink::for_path(binary_path);
        println!("  {} {link}", style::paint_verb("→", Tone::Accent));
    }

    if style::is_verbose() {
        print_verbose_breakdown(stats);
    }
}

fn print_verbose_breakdown(stats: &BuildStats) {
    let line = |label: &str, ms: u128| {
        println!(
            "{}",
            style::dim(format!("  {label:>8} {}", format_duration(ms)))
        );
    };
    line("resolve", stats.resolution_time_ms);
    line("analyze", stats.analysis_time_ms);
    line("execute", stats.execution_time_ms);
    if stats.linking_time_ms > 0 {
        line("link", stats.linking_time_ms);
    }
}

#[allow(clippy::cast_precision_loss)]
fn format_duration(ms: u128) -> String {
    if ms < 1000 {
        format!("{ms}ms")
    } else if ms < 60_000 {
        format!("{:.2}s", ms as f64 / 1000.0)
    } else {
        let seconds = ms / 1000;
        let minutes = seconds / 60;
        let remaining_seconds = seconds % 60;
        format!("{minutes}m {remaining_seconds}s")
    }
}
