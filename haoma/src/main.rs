#![warn(clippy::pedantic)]

use tracing_appender::rolling;
use tracing_subscriber::{EnvFilter, fmt, layer::SubscriberExt};

mod build;
mod cli;
mod config;
mod logging;

fn main() {
    let cli = cli::parse();
    let _guard = if let Some(log_file) = cli.log_file {
        if log_file.exists() {
            logging::output_err(
                "Log file already exists. Please remove it or choose a different file.",
            );
            std::process::exit(1);
        }
        let file_appender = rolling::never(".", log_file);
        let (non_blocking, guard) = tracing_appender::non_blocking(file_appender);

        let file_layer = fmt::layer().with_writer(non_blocking).compact();
        let subscriber = tracing_subscriber::registry()
            .with(EnvFilter::from_default_env().add_directive("debug".parse().unwrap()))
            .with(file_layer);
        tracing::subscriber::set_global_default(subscriber).expect("Failed to set subscriber");
        Some(guard)
    } else {
        None
    };
    tracing::debug!(
        "Executing command: {}",
        std::env::args().collect::<Vec<_>>().join(" ")
    );

    cli::execute(&cli.command);
}
