use ratatui::{
    Frame,
    layout::{Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, Clear, Gauge, List, ListItem, Paragraph},
};

use crate::tui::app::{App, AppMode, ConfirmAction};

pub fn draw(frame: &mut Frame, app: &App) {
    match app.mode {
        AppMode::Building => draw_build_screen(frame, app),
        _ => draw_normal_screen(frame, app),
    }
}

fn draw_normal_screen(frame: &mut Frame, app: &App) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(3), // Header
            Constraint::Min(0),    // Main content
            Constraint::Length(3), // Footer/status
        ])
        .split(frame.area());

    draw_header(frame, app, chunks[0]);
    draw_versions(frame, app, chunks[1]);
    draw_footer(frame, app, chunks[2]);

    // Draw confirmation dialog if needed
    if app.mode == AppMode::Confirming {
        draw_confirm_dialog(frame, app);
    }
}

fn draw_build_screen(frame: &mut Frame, app: &App) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(3), // Header
            Constraint::Length(3), // Progress bar
            Constraint::Min(0),    // Build output
            Constraint::Length(3), // Footer
        ])
        .split(frame.area());

    draw_header(frame, app, chunks[0]);
    draw_progress_bar(frame, app, chunks[1]);
    draw_build_output(frame, app, chunks[2]);
    draw_build_footer(frame, app, chunks[3]);
}

fn draw_header(frame: &mut Frame, app: &App, area: Rect) {
    let project_indicator = if app.project_root.is_some() {
        Span::styled(" [project detected]", Style::default().fg(Color::Green))
    } else {
        Span::styled(" [no project]", Style::default().fg(Color::DarkGray))
    };

    let header = Paragraph::new(Line::from(vec![
        Span::styled(
            "svm",
            Style::default()
                .fg(Color::Cyan)
                .add_modifier(Modifier::BOLD),
        ),
        Span::raw(" - Soma Version Manager"),
        project_indicator,
    ]))
    .block(Block::default().borders(Borders::ALL));

    frame.render_widget(header, area);
}

fn draw_versions(frame: &mut Frame, app: &App, area: Rect) {
    if app.versions.is_empty() {
        let mut lines = vec![Line::from("No versions installed."), Line::from("")];

        if app.project_root.is_some() {
            lines.push(Line::from(Span::styled(
                "Press 'b' to build dev version from source.",
                Style::default().fg(Color::Yellow),
            )));
        } else {
            lines.push(Line::from(
                "Run 'svm dev' from a Soma project to build from source.",
            ));
        }

        let empty =
            Paragraph::new(lines).block(Block::default().title("Versions").borders(Borders::ALL));

        frame.render_widget(empty, area);
        return;
    }

    let items: Vec<ListItem> = app
        .versions
        .iter()
        .enumerate()
        .map(|(i, version)| {
            let is_current = Some(version) == app.current.as_ref();
            let is_selected = i == app.selected;

            let marker = if is_current { "*" } else { " " };
            let content = format!("{marker} {version}");

            let style = match (is_selected, is_current) {
                (true, true) => Style::default()
                    .fg(Color::Green)
                    .add_modifier(Modifier::BOLD | Modifier::REVERSED),
                (true, false) => Style::default().add_modifier(Modifier::REVERSED),
                (false, true) => Style::default()
                    .fg(Color::Green)
                    .add_modifier(Modifier::BOLD),
                (false, false) => Style::default(),
            };

            ListItem::new(content).style(style)
        })
        .collect();

    let list = List::new(items)
        .block(
            Block::default()
                .title("Installed Versions")
                .borders(Borders::ALL),
        )
        .highlight_style(Style::default().add_modifier(Modifier::REVERSED));

    frame.render_widget(list, area);
}

fn draw_footer(frame: &mut Frame, app: &App, area: Rect) {
    let help_text = if app.project_root.is_some() {
        "j/k: navigate | Enter: use | d: delete | b: build dev | r: refresh | q: quit"
    } else {
        "j/k: navigate | Enter: use | d: delete | r: refresh | q: quit"
    };

    let message = app.message.as_deref().unwrap_or(help_text);

    let footer = Paragraph::new(message)
        .style(Style::default().fg(Color::Gray))
        .block(Block::default().borders(Borders::ALL));

    frame.render_widget(footer, area);
}

#[allow(clippy::cast_precision_loss)]
fn draw_progress_bar(frame: &mut Frame, app: &App, area: Rect) {
    let (label, ratio) = if let Some(ref state) = app.build_state {
        let ratio = if state.components_total > 0 {
            state.components_done as f64 / state.components_total as f64
        } else {
            0.0
        };
        let label = format!(
            "Building {} ({}/{})",
            state.component, state.components_done, state.components_total
        );
        (label, ratio)
    } else {
        ("Building...".to_string(), 0.0)
    };

    let gauge = Gauge::default()
        .block(Block::default().title("Progress").borders(Borders::ALL))
        .gauge_style(Style::default().fg(Color::Cyan))
        .ratio(ratio)
        .label(label);

    frame.render_widget(gauge, area);
}

fn draw_build_output(frame: &mut Frame, app: &App, area: Rect) {
    let lines: Vec<Line> = if let Some(ref state) = app.build_state {
        state
            .output_lines
            .iter()
            .map(|s| {
                let style = if s.starts_with("[Building ") {
                    Style::default()
                        .fg(Color::Cyan)
                        .add_modifier(Modifier::BOLD)
                } else if s.contains("error") || s.contains("Error") {
                    Style::default().fg(Color::Red)
                } else if s.contains("warning") || s.contains("Warning") {
                    Style::default().fg(Color::Yellow)
                } else if s.starts_with("Linked ") {
                    Style::default().fg(Color::Green)
                } else {
                    Style::default()
                };
                Line::styled(s.clone(), style)
            })
            .collect()
    } else {
        vec![Line::from("Starting build...")]
    };

    // Show last N lines that fit in the area
    let visible_height = area.height.saturating_sub(2) as usize; // Account for borders
    let start = lines.len().saturating_sub(visible_height);
    let visible_lines: Vec<Line> = lines.into_iter().skip(start).collect();

    let output = Paragraph::new(visible_lines)
        .block(Block::default().title("Build Output").borders(Borders::ALL));

    frame.render_widget(output, area);
}

fn draw_build_footer(frame: &mut Frame, app: &App, area: Rect) {
    let text = if let Some(ref state) = app.build_state {
        if state.is_complete {
            if state.success {
                "Build complete! Press Esc or q to continue."
            } else {
                "Build failed. Press Esc or q to continue."
            }
        } else {
            "Building... Please wait."
        }
    } else {
        "Initializing..."
    };

    let style = if let Some(ref state) = app.build_state {
        if state.is_complete {
            if state.success {
                Style::default().fg(Color::Green)
            } else {
                Style::default().fg(Color::Red)
            }
        } else {
            Style::default().fg(Color::Yellow)
        }
    } else {
        Style::default()
    };

    let footer = Paragraph::new(text)
        .style(style)
        .block(Block::default().borders(Borders::ALL));

    frame.render_widget(footer, area);
}

fn draw_confirm_dialog(frame: &mut Frame, app: &App) {
    let area = centered_rect(50, 25, frame.area());

    let message = match &app.confirm_action {
        Some(ConfirmAction::Use(v)) => format!("Switch to version {v}?"),
        Some(ConfirmAction::Uninstall(v)) => format!("Uninstall version {v}?"),
        Some(ConfirmAction::BuildDev) => "Build dev version from source?".to_string(),
        None => "Confirm?".to_string(),
    };

    let dialog = Paragraph::new(vec![
        Line::from(""),
        Line::from(message),
        Line::from(""),
        Line::from(Span::styled(
            "(y)es / (n)o",
            Style::default().fg(Color::Yellow),
        )),
    ])
    .block(
        Block::default()
            .title("Confirm")
            .borders(Borders::ALL)
            .style(Style::default().bg(Color::DarkGray)),
    )
    .style(Style::default().fg(Color::White));

    frame.render_widget(Clear, area);
    frame.render_widget(dialog, area);
}

fn centered_rect(percent_x: u16, percent_y: u16, area: Rect) -> Rect {
    let popup_layout = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Percentage((100 - percent_y) / 2),
            Constraint::Percentage(percent_y),
            Constraint::Percentage((100 - percent_y) / 2),
        ])
        .split(area);

    Layout::default()
        .direction(Direction::Horizontal)
        .constraints([
            Constraint::Percentage((100 - percent_x) / 2),
            Constraint::Percentage(percent_x),
            Constraint::Percentage((100 - percent_x) / 2),
        ])
        .split(popup_layout[1])[1]
}
