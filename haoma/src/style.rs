use std::fmt::{self, Display};
use std::io::{IsTerminal, Write};
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum ColorMode {
    #[default]
    Auto,
    Always,
    Never,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Verbosity {
    Quiet,
    #[default]
    Normal,
    Verbose,
}

static VERBOSITY: AtomicU8 = AtomicU8::new(1);
static COLOR_ENABLED: AtomicBool = AtomicBool::new(true);

pub fn init(color: ColorMode, verbosity: Verbosity) {
    VERBOSITY.store(verbosity as u8, Ordering::Relaxed);

    let enabled = match color {
        ColorMode::Always => true,
        ColorMode::Never => false,
        ColorMode::Auto => {
            std::env::var_os("NO_COLOR").is_none() && std::io::stdout().is_terminal()
        }
    };
    COLOR_ENABLED.store(enabled, Ordering::Relaxed);
}

pub fn verbosity() -> Verbosity {
    match VERBOSITY.load(Ordering::Relaxed) {
        0 => Verbosity::Quiet,
        2 => Verbosity::Verbose,
        _ => Verbosity::Normal,
    }
}

pub fn is_quiet() -> bool {
    verbosity() == Verbosity::Quiet
}

pub fn is_verbose() -> bool {
    verbosity() == Verbosity::Verbose
}

fn color_enabled() -> bool {
    COLOR_ENABLED.load(Ordering::Relaxed)
}

#[derive(Clone, Copy)]
pub enum Tone {
    Progress,
    Success,
    Note,
    Accent,
    Error,
}

const RESET: &str = "\x1b[0m";
const DIM: &str = "\x1b[2m";
const BOLD_GREEN: &str = "\x1b[1;32m";
const BOLD_CYAN: &str = "\x1b[1;36m";
const CYAN: &str = "\x1b[36m";
const BOLD_RED: &str = "\x1b[1;31m";
const RED: &str = "\x1b[31m";
const BOLD_YELLOW: &str = "\x1b[1;33m";

pub fn format_status(tone: Tone, verb: &str, subject: impl Display) -> String {
    let subject = subject.to_string();
    match tone {
        Tone::Error => paint_full(&format!("{verb} {subject}"), tone),
        _ => format!("{} {}", paint_verb(verb, tone), dim(&subject)),
    }
}

pub fn format_status_with_meta(
    tone: Tone,
    verb: &str,
    subject: impl Display,
    meta: impl Display,
) -> String {
    let subject = subject.to_string();
    let meta = meta.to_string();
    match tone {
        Tone::Error => paint_full(&format!("{verb} {subject} {meta}"), tone),
        _ => format!(
            "{} {} {}",
            paint_verb(verb, tone),
            dim(&subject),
            dim(&meta)
        ),
    }
}

pub fn paint_verb(verb: &str, tone: Tone) -> String {
    if !color_enabled() {
        return verb.to_string();
    }
    let code = match tone {
        Tone::Progress => BOLD_CYAN,
        Tone::Success => BOLD_GREEN,
        Tone::Note => DIM,
        Tone::Accent => CYAN,
        Tone::Error => BOLD_RED,
    };
    format!("{code}{verb}{RESET}")
}

fn paint_full(text: &str, tone: Tone) -> String {
    if !color_enabled() {
        return text.to_string();
    }
    match tone {
        Tone::Error => format!("{RED}{text}{RESET}"),
        _ => format!("{DIM}{text}{RESET}"),
    }
}

pub fn dim(text: impl Display) -> String {
    if color_enabled() {
        format!("{DIM}{text}{RESET}")
    } else {
        text.to_string()
    }
}

pub fn status(tone: Tone, verb: &str, subject: impl Display) {
    if is_quiet() {
        return;
    }
    println!("{}", format_status(tone, verb, subject));
    let _ = std::io::stdout().flush();
}

pub fn status_meta(tone: Tone, verb: &str, subject: impl Display, meta: impl Display) {
    if is_quiet() {
        return;
    }
    println!("{}", format_status_with_meta(tone, verb, subject, meta));
    let _ = std::io::stdout().flush();
}

pub fn error(msg: impl Display) {
    let prefix = if color_enabled() {
        format!("{BOLD_RED}error:{RESET}")
    } else {
        "error:".to_string()
    };
    eprintln!("{prefix} {msg}");
}

pub fn warning(msg: impl Display) {
    let prefix = if color_enabled() {
        format!("{BOLD_YELLOW}warning:{RESET}")
    } else {
        "warning:".to_string()
    };
    eprintln!("{prefix} {msg}");
}

pub struct Hyperlink<'a> {
    url: String,
    text: &'a str,
}

impl<'a> Hyperlink<'a> {
    pub fn for_path(path: &'a std::path::Path) -> Hyperlink<'a> {
        let abs = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        let url = format!("file://{}", abs.display());
        Hyperlink {
            url,
            text: path_str(path),
        }
    }
}

impl Display for Hyperlink<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if color_enabled() && supports_hyperlinks::on(supports_hyperlinks::Stream::Stdout) {
            write!(f, "\x1b]8;;{}\x1b\\{}\x1b]8;;\x1b\\", self.url, self.text)
        } else {
            write!(f, "{}", self.text)
        }
    }
}

fn path_str(path: &std::path::Path) -> &str {
    path.to_str().unwrap_or("<non-utf8 path>")
}
