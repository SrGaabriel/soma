use std::path::Path;

use colored::Colorize;

use crate::{
    build::{BuildStats, build_project},
    cli::parse_manifest,
    logging::{output_debug, output_err},
};

pub fn execute(path: &Path) {
    let manifest = parse_manifest(path);
    output_debug("Successfully read manifest file");
    match build_project(path, &manifest) {
        Ok(build) => {
            print_build_success(&build);
        }
        Err(e) => {
            output_err(&format!("Build failed: {}", e));
        }
    }
}

fn print_build_success(stats: &BuildStats) {
    println!();
    println!(
        "{}",
        "╔═══════════════════════════════════════════════════════════════╗".bright_green()
    );
    println!(
        "{}",
        "║                     BUILD SUCCESSFUL ✓                        ║"
            .bright_green()
            .bold()
    );
    println!(
        "{}",
        "╚═══════════════════════════════════════════════════════════════╝".bright_green()
    );
    println!();

    println!("{}", "  📦 Module Statistics".cyan().bold());
    println!(
        "     {} {}",
        "Total modules:".bright_white(),
        stats.total_modules.to_string().yellow()
    );
    println!(
        "     {} {}",
        "Built:".bright_white(),
        format!(
            "{} module{}",
            stats.modules_built,
            if stats.modules_built != 1 { "s" } else { "" }
        )
        .green()
    );
    println!(
        "     {} {} {}",
        "Cached:".bright_white(),
        format!(
            "{} module{}",
            stats.modules_cached,
            if stats.modules_cached != 1 { "s" } else { "" }
        )
        .bright_blue(),
        if stats.total_modules > 0 {
            format!(
                "({}% reused)",
                (stats.modules_cached * 100) / stats.total_modules
            )
            .dimmed()
            .to_string()
        } else {
            String::new()
        }
    );
    println!();

    println!("{}", "  ⏱  Timing Breakdown".cyan().bold());
    println!(
        "     {} {}",
        "Resolution:".bright_white(),
        format_duration(stats.resolution_time_ms)
    );
    println!(
        "     {} {}",
        "Analysis:".bright_white(),
        format_duration(stats.analysis_time_ms)
    );
    println!(
        "     {} {}",
        "Execution:".bright_white(),
        format_duration(stats.execution_time_ms).green()
    );
    if stats.linking_time_ms > 0 {
        println!(
            "     {} {}",
            "Linking:".bright_white(),
            format_duration(stats.linking_time_ms)
        );
    }
    println!("     {}", "─".repeat(40).dimmed());
    println!(
        "     {} {}",
        "Total:".bright_white().bold(),
        format_duration(stats.total_time_ms).yellow().bold()
    );
    println!();

    if let Some(binary_path) = &stats.final_binary_path {
        println!("{}", "  🎯 Output".cyan().bold());
        println!(
            "     {} {}",
            "Binary:".bright_white(),
            binary_path.display().to_string().green()
        );
        println!();
    }

    let efficiency = if stats.total_modules > 0 {
        (stats.modules_cached * 100) / stats.total_modules
    } else {
        0
    };

    if efficiency > 0 {
        println!(
            "  {} {}",
            "⚡".yellow(),
            format!(
                "Build completed in {} ({}% cache hit rate)",
                format_duration(stats.total_time_ms),
                efficiency
            )
            .dimmed()
        );
    } else {
        println!(
            "  {} {}",
            "✓".green(),
            format!(
                "Build completed in {}",
                format_duration(stats.total_time_ms)
            )
            .dimmed()
        );
    }
    println!();
}

fn format_duration(ms: u128) -> String {
    if ms < 1000 {
        format!("{}ms", ms)
    } else if ms < 60_000 {
        format!("{:.2}s", ms as f64 / 1000.0)
    } else {
        let seconds = ms / 1000;
        let minutes = seconds / 60;
        let remaining_seconds = seconds % 60;
        format!("{}m {}s", minutes, remaining_seconds)
    }
}
