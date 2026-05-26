use std::collections::HashMap;
use std::time::Duration;

use indicatif::{MultiProgress, ProgressBar, ProgressDrawTarget, ProgressStyle};

use crate::style;

const TICK_INTERVAL: Duration = Duration::from_millis(80);
const SPINNER_CHARS: &str = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏ ";

pub struct ProgressDisplay {
    multi: MultiProgress,
    header: ProgressBar,
    workers: HashMap<String, ProgressBar>,
    enabled: bool,
}

impl ProgressDisplay {
    pub fn new(total_to_build: usize) -> Self {
        let enabled = !style::is_quiet()
            && total_to_build > 0
            && std::io::IsTerminal::is_terminal(&std::io::stderr());

        let target = if enabled {
            ProgressDrawTarget::stderr()
        } else {
            ProgressDrawTarget::hidden()
        };
        let multi = MultiProgress::with_draw_target(target);

        let header = multi.add(ProgressBar::new(total_to_build as u64));
        header.set_style(
            ProgressStyle::with_template(
                "{spinner:.cyan.bold} {msg:.cyan.bold}building [{bar:20.cyan/dim}] {pos:.dim}/{len:.dim}",
            )
            .expect("valid template")
            .tick_chars(SPINNER_CHARS)
            .progress_chars("=> "),
        );
        header.enable_steady_tick(TICK_INTERVAL);

        Self {
            multi,
            header,
            workers: HashMap::new(),
            enabled,
        }
    }

    pub fn start(&mut self, module: &str, version: &str) {
        if !self.enabled {
            return;
        }
        let pb = self.multi.add(ProgressBar::new_spinner());
        pb.set_style(
            ProgressStyle::with_template("  {spinner:.cyan.bold} {prefix:.cyan.bold} {msg:.dim}")
                .expect("valid template")
                .tick_chars(SPINNER_CHARS),
        );
        pb.set_prefix("compiling");
        pb.set_message(format!("{module} v{version}"));
        pb.enable_steady_tick(TICK_INTERVAL);
        self.workers.insert(module.to_string(), pb);
    }

    pub fn finish(&mut self, module: &str) {
        if let Some(pb) = self.workers.remove(module) {
            pb.finish_and_clear();
            self.multi.remove(&pb);
        }
        if self.enabled {
            self.header.inc(1);
        }
    }

    pub fn print_above(&self, line: &str) {
        if self.enabled {
            let _ = self.multi.println(line);
        } else {
            println!("{line}");
        }
    }

    pub fn finish_all(&mut self) {
        for (_, pb) in self.workers.drain() {
            pb.finish_and_clear();
            self.multi.remove(&pb);
        }
        self.header.finish_and_clear();
        let _ = self.multi.clear();
    }
}

impl Drop for ProgressDisplay {
    fn drop(&mut self) {
        self.finish_all();
    }
}
