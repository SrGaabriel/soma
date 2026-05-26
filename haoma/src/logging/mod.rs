use std::fmt::Display;

use crate::style;

pub fn output_err(text: impl Display) {
    let text = text.to_string();
    style::error(&text);
    tracing::error!("{text}");
}

#[allow(dead_code)]
pub fn output_warning(text: impl Display) {
    let text = text.to_string();
    style::warning(&text);
    tracing::warn!("{text}");
}

pub fn output_debug(text: impl Display) {
    tracing::debug!("{text}");
}
