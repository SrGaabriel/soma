use colored::{Color, Colorize};

pub fn output_err(text: &str) {
    pretty_print("error", "⛔", colored::Color::Red, text);
    tracing::error!("{}", text);
}

#[allow(dead_code)]
pub fn output_warning(text: &str) {
    pretty_print("warn", "⚠️", colored::Color::Yellow, text);
    tracing::warn!("{}", text);
}

pub fn output_debug(text: &str) {
    tracing::debug!("{}", text);
}

pub fn output_ok(text: &str) {
    pretty_print("success", "✅", colored::Color::Green, text);
    tracing::info!("{}", text);
}

pub fn pretty_print(prefix: &str, emoji: &str, color: Color, text: &str) {
    println!(
        "{} {} {}",
        format!("[{prefix}]").color(color).bold(),
        emoji,
        text
    );
}
