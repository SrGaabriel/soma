use std::io::{self, BufRead, BufReader};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::mpsc::{self, Receiver, Sender};
use std::thread;
use std::time::Duration;

use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode, KeyEventKind},
    execute,
    terminal::{EnterAlternateScreen, LeaveAlternateScreen, disable_raw_mode, enable_raw_mode},
};
use ratatui::{Terminal, backend::CrosstermBackend};

use crate::core::{
    BuildConfig, ComponentConfig, Result, SvmDirs, SvmError, Target, Version, find_project_root,
};
use crate::tui::ui;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AppMode {
    Normal,
    Building,
    Confirming,
}

pub struct App {
    pub dirs: SvmDirs,
    pub target: Target,
    pub versions: Vec<Version>,
    pub current: Option<Version>,
    pub selected: usize,
    pub mode: AppMode,
    pub message: Option<String>,
    pub should_quit: bool,
    pub confirm_action: Option<ConfirmAction>,
    pub build_state: Option<BuildState>,
    pub project_root: Option<PathBuf>,
}

#[derive(Debug, Clone)]
pub enum ConfirmAction {
    Uninstall(Version),
    Use(Version),
    BuildDev,
}

pub struct BuildState {
    pub component: String,
    pub output_lines: Vec<String>,
    pub is_complete: bool,
    pub success: bool,
    pub components_done: usize,
    pub components_total: usize,
    pub receiver: Receiver<BuildMessage>,
}

pub enum BuildMessage {
    Output(String),
    ComponentDone { success: bool },
    AllDone { success: bool },
}

impl App {
    pub fn new() -> Result<Self> {
        let dirs = SvmDirs::new()?;
        dirs.ensure_dirs()?;
        let target = Target::host();
        let versions = dirs.installed_versions()?;
        let current = dirs.current_version(&target)?;
        let project_root = find_project_root();

        Ok(Self {
            dirs,
            target,
            versions,
            current,
            selected: 0,
            mode: AppMode::Normal,
            message: None,
            should_quit: false,
            confirm_action: None,
            build_state: None,
            project_root,
        })
    }

    pub fn refresh(&mut self) -> Result<()> {
        self.versions = self.dirs.installed_versions()?;
        self.current = self.dirs.current_version(&self.target)?;
        if self.selected >= self.versions.len() && !self.versions.is_empty() {
            self.selected = self.versions.len() - 1;
        }
        Ok(())
    }

    pub fn selected_version(&self) -> Option<&Version> {
        self.versions.get(self.selected)
    }

    pub fn select_next(&mut self) {
        if !self.versions.is_empty() {
            self.selected = (self.selected + 1) % self.versions.len();
        }
    }

    pub fn select_prev(&mut self) {
        if !self.versions.is_empty() {
            self.selected = self
                .selected
                .checked_sub(1)
                .unwrap_or(self.versions.len() - 1);
        }
    }

    pub fn start_dev_build(&mut self) -> Result<()> {
        let project_root = self.project_root.clone().ok_or(SvmError::ProjectNotFound)?;

        let config = BuildConfig::load(&project_root)?;
        let components: Vec<ComponentConfig> = config.iter().cloned().collect();
        let total = components.len();

        if total == 0 {
            self.message = Some("No components found to build".to_string());
            return Ok(());
        }

        let (tx, rx) = mpsc::channel();
        let dirs = self.dirs.clone();
        let target = self.target.clone();

        thread::spawn(move || {
            run_build(project_root, components, dirs, target, tx);
        });

        self.build_state = Some(BuildState {
            component: "Starting...".to_string(),
            output_lines: Vec::new(),
            is_complete: false,
            success: false,
            components_done: 0,
            components_total: total,
            receiver: rx,
        });
        self.mode = AppMode::Building;

        Ok(())
    }

    pub fn poll_build(&mut self) {
        if let Some(ref mut state) = self.build_state {
            while let Ok(msg) = state.receiver.try_recv() {
                match msg {
                    BuildMessage::Output(line) => {
                        if line.starts_with("[Building ")
                            && let Some(end) = line.find(']')
                        {
                            state.component = line[10..end].to_string();
                        }
                        state.output_lines.push(line);
                        if state.output_lines.len() > 100 {
                            state.output_lines.remove(0);
                        }
                    }
                    BuildMessage::ComponentDone { success: _ } => {
                        state.components_done += 1;
                    }
                    BuildMessage::AllDone { success } => {
                        state.is_complete = true;
                        state.success = success;
                    }
                }
            }
        }
    }

    pub fn handle_key(&mut self, key: KeyCode) -> Result<()> {
        match self.mode {
            AppMode::Normal => match key {
                KeyCode::Char('q') | KeyCode::Esc => self.should_quit = true,
                KeyCode::Char('j') | KeyCode::Down => self.select_next(),
                KeyCode::Char('k') | KeyCode::Up => self.select_prev(),
                KeyCode::Enter => {
                    if let Some(v) = self.selected_version().cloned() {
                        self.confirm_action = Some(ConfirmAction::Use(v));
                        self.mode = AppMode::Confirming;
                    }
                }
                KeyCode::Char('d') => {
                    if let Some(v) = self.selected_version().cloned() {
                        if Some(&v) != self.current.as_ref() {
                            self.confirm_action = Some(ConfirmAction::Uninstall(v));
                            self.mode = AppMode::Confirming;
                        } else {
                            self.message = Some("Cannot uninstall the active version".to_string());
                        }
                    }
                }
                KeyCode::Char('b') => {
                    if self.project_root.is_some() {
                        self.confirm_action = Some(ConfirmAction::BuildDev);
                        self.mode = AppMode::Confirming;
                    } else {
                        self.message = Some("Not in a Soma project directory".to_string());
                    }
                }
                KeyCode::Char('r') => {
                    self.refresh()?;
                    self.message = Some("Refreshed".to_string());
                }
                _ => {}
            },
            AppMode::Confirming => match key {
                KeyCode::Char('y') | KeyCode::Enter => {
                    if let Some(action) = self.confirm_action.take() {
                        match action {
                            ConfirmAction::Use(v) => {
                                self.dirs.set_current(&v, &self.target)?;
                                self.current = Some(v.clone());
                                self.message = Some(format!("Switched to {}", v));
                            }
                            ConfirmAction::Uninstall(v) => {
                                self.dirs.remove_version(&v)?;
                                self.message = Some(format!("Uninstalled {}", v));
                                self.refresh()?;
                            }
                            ConfirmAction::BuildDev => {
                                self.start_dev_build()?;
                                return Ok(());
                            }
                        }
                    }
                    self.mode = AppMode::Normal;
                }
                KeyCode::Char('n') | KeyCode::Esc => {
                    self.confirm_action = None;
                    self.mode = AppMode::Normal;
                }
                _ => {}
            },
            AppMode::Building => {
                if (key == KeyCode::Esc || key == KeyCode::Char('q'))
                    && let Some(ref state) = self.build_state
                    && state.is_complete
                {
                    if state.success {
                        self.message = Some("Build completed successfully".to_string());
                        self.refresh()?;
                    } else {
                        self.message = Some("Build failed".to_string());
                    }
                    self.build_state = None;
                    self.mode = AppMode::Normal;
                }
                // if not complete, ignore esc (can't cancel mid-build)
            }
        }
        Ok(())
    }
}

fn run_build(
    project_root: PathBuf,
    components: Vec<ComponentConfig>,
    dirs: SvmDirs,
    target: Target,
    tx: Sender<BuildMessage>,
) {
    use std::fs;

    let version = Version::Dev;
    let bin_dir = dirs.bin_dir(&version, &target);

    if let Err(e) = fs::create_dir_all(&bin_dir) {
        let _ = tx.send(BuildMessage::Output(format!("Error creating dir: {}", e)));
        let _ = tx.send(BuildMessage::AllDone { success: false });
        return;
    }

    let mut all_success = true;

    for component in &components {
        let _ = tx.send(BuildMessage::Output(format!(
            "[Building {}]",
            component.name
        )));

        let work_dir = project_root.join(&component.path);
        let parts: Vec<&str> = component.build_command.split_whitespace().collect();

        if parts.is_empty() {
            let _ = tx.send(BuildMessage::Output("Empty build command".to_string()));
            let _ = tx.send(BuildMessage::ComponentDone { success: false });
            all_success = false;
            continue;
        }

        let (cmd, args) = parts.split_first().unwrap();

        let child_result = Command::new(cmd)
            .args(args.iter())
            .current_dir(&work_dir)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn();

        let mut child: Child = match child_result {
            Ok(c) => c,
            Err(e) => {
                let _ = tx.send(BuildMessage::Output(format!("Failed to start: {}", e)));
                let _ = tx.send(BuildMessage::ComponentDone { success: false });
                all_success = false;
                continue;
            }
        };

        if let Some(stdout) = child.stdout.take() {
            let tx_clone = tx.clone();
            let reader = BufReader::new(stdout);
            for line in reader.lines().map_while(|l| l.ok()) {
                let _ = tx_clone.send(BuildMessage::Output(line));
            }
        }

        if let Some(stderr) = child.stderr.take() {
            let tx_clone = tx.clone();
            let reader = BufReader::new(stderr);
            for line in reader.lines().map_while(|l| l.ok()) {
                let _ = tx_clone.send(BuildMessage::Output(line));
            }
        }

        let status = child.wait();
        let success = status.map(|s| s.success()).unwrap_or(false);

        if success {
            let src = work_dir.join(&component.binary_path);
            let dest = bin_dir.join(&component.name);

            if dest.exists() || dest.is_symlink() {
                let _ = fs::remove_file(&dest);
            }

            #[cfg(unix)]
            {
                if let Err(e) = std::os::unix::fs::symlink(&src, &dest) {
                    let _ = tx.send(BuildMessage::Output(format!("Symlink error: {}", e)));
                } else {
                    let _ = tx.send(BuildMessage::Output(format!(
                        "Linked {} -> {}",
                        component.name,
                        src.display()
                    )));
                }
            }

            #[cfg(windows)]
            {
                if let Err(e) = std::os::windows::fs::symlink_file(&src, &dest) {
                    let _ = tx.send(BuildMessage::Output(format!("Symlink error: {}", e)));
                }
            }
        } else {
            all_success = false;
        }

        let _ = tx.send(BuildMessage::ComponentDone { success });
    }

    if all_success {
        let _ = dirs.set_current(&version, &target);
        let _ = tx.send(BuildMessage::Output(
            "\nDev mode active. Binaries linked.".to_string(),
        ));
    }

    let _ = tx.send(BuildMessage::AllDone {
        success: all_success,
    });
}

impl Clone for SvmDirs {
    fn clone(&self) -> Self {
        Self::new().expect("Failed to clone SvmDirs")
    }
}

pub fn run_tui() -> Result<()> {
    enable_raw_mode().map_err(|e| SvmError::Io {
        path: std::path::PathBuf::from("terminal"),
        source: e,
    })?;

    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture).map_err(|e| SvmError::Io {
        path: std::path::PathBuf::from("terminal"),
        source: e,
    })?;

    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend).map_err(|e| SvmError::Io {
        path: std::path::PathBuf::from("terminal"),
        source: e,
    })?;

    let mut app = App::new()?;

    let result = run_app(&mut terminal, &mut app);

    disable_raw_mode().ok();
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )
    .ok();
    terminal.show_cursor().ok();

    result
}

fn run_app(terminal: &mut Terminal<CrosstermBackend<io::Stdout>>, app: &mut App) -> Result<()> {
    loop {
        if app.mode == AppMode::Building {
            app.poll_build();
        }

        terminal
            .draw(|f| ui::draw(f, app))
            .map_err(|e| SvmError::Io {
                path: std::path::PathBuf::from("terminal"),
                source: e,
            })?;

        if event::poll(Duration::from_millis(50)).map_err(|e| SvmError::Io {
            path: std::path::PathBuf::from("terminal"),
            source: e,
        })? && let Event::Key(key) = event::read().map_err(|e| SvmError::Io {
            path: std::path::PathBuf::from("terminal"),
            source: e,
        })? && key.kind == KeyEventKind::Press
        {
            app.handle_key(key.code)?;
        }

        if app.should_quit {
            break;
        }
    }

    Ok(())
}
