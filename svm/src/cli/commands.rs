use std::path::PathBuf;
use std::process::Command;
use std::{fs, path::Path};

use directories::BaseDirs;

use crate::core::{
    BuildConfig, ComponentConfig, LibraryConfig, Result, SvmDirs, SvmError, Target, Version,
    find_project_root,
};

const HWND_BROADCAST: *mut std::ffi::c_void = 0xffff as *mut std::ffi::c_void;
const WM_SETTINGCHANGE: u32 = 0x001A;
const SMTO_ABORTIFHUNG: u32 = 0x0002;

#[link(name = "user32")]
unsafe extern "system" {
    fn SendMessageTimeoutW(
        hwnd: *mut std::ffi::c_void,
        msg: u32,
        wparam: usize,
        lparam: *const u16,
        flags: u32,
        timeout: u32,
        result: *mut usize,
    ) -> isize;
}

pub struct CommandRunner {
    dirs: SvmDirs,
    target: Target,
}

impl CommandRunner {
    pub fn new() -> Result<Self> {
        let dirs = SvmDirs::new()?;
        dirs.ensure_dirs()?;
        Ok(Self {
            dirs,
            target: Target::host(),
        })
    }

    pub fn install(&self, version_str: &str) -> Result<()> {
        let _version: Version = version_str
            .parse()
            .map_err(|e| SvmError::InvalidConfig(format!("Invalid version: {e}")))?;

        // todo: remote installation
        Err(SvmError::RemoteNotImplemented)
    }

    pub fn dev(&self, path: Option<PathBuf>, copy: bool, only: Option<&Vec<String>>) -> Result<()> {
        let project_root = path
            .or_else(find_project_root)
            .ok_or(SvmError::ProjectNotFound)?;

        let config = BuildConfig::load(&project_root)?;
        let version = Version::Dev;
        let bin_dir = self.dirs.bin_dir(&version, &self.target);
        let lib_dir = self.dirs.lib_dir(&version, &self.target);

        fs::create_dir_all(&bin_dir).map_err(|e| SvmError::io(&bin_dir, e))?;
        fs::create_dir_all(&lib_dir).map_err(|e| SvmError::io(&lib_dir, e))?;

        let components: Vec<&ComponentConfig> = config
            .iter()
            .filter(|c| {
                only.as_ref()
                    .is_none_or(|names| names.iter().any(|n| n == &c.name))
            })
            .collect();

        let libraries: Vec<&LibraryConfig> = config
            .iter_libraries()
            .filter(|l| {
                only.as_ref()
                    .is_none_or(|names| names.iter().any(|n| n == &l.name))
            })
            .collect();

        if components.is_empty() && libraries.is_empty() {
            return Err(SvmError::InvalidConfig(
                "No matching components found".to_string(),
            ));
        }

        for component in components {
            let work_dir = project_root.join(&component.path);
            let src = if cfg!(windows) {
                work_dir.join(component.binary_path.with_extension("exe"))
            } else {
                work_dir.join(&component.binary_path)
            };
            let dest_name = if cfg!(windows) {
                format!("{}.exe", component.name)
            } else {
                component.name.clone()
            };
            let dest = bin_dir.join(&dest_name);

            if !src.exists() {
                println!("Building {}...", component.name);
                self.build_component(component, &work_dir)?;
            }

            if dest.exists() || dest.is_symlink() {
                fs::remove_file(&dest).map_err(|e| SvmError::io(&dest, e))?;
            }

            if copy {
                fs::copy(&src, &dest).map_err(|e| SvmError::io(&dest, e))?;

                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt;
                    let mut perms = fs::metadata(&dest)
                        .map_err(|e| SvmError::io(&dest, e))?
                        .permissions();
                    perms.set_mode(0o755);
                    fs::set_permissions(&dest, perms).map_err(|e| SvmError::io(&dest, e))?;
                }

                println!("  {} -> {} (copied)", component.name, dest.display());
            } else {
                #[cfg(unix)]
                std::os::unix::fs::symlink(&src, &dest).map_err(|e| SvmError::io(&dest, e))?;

                #[cfg(windows)]
                std::os::windows::fs::symlink_file(&src, &dest)
                    .map_err(|e| SvmError::io(&dest, e))?;

                println!("  {} -> {} (linked)", component.name, src.display());
            }
        }

        // Handle library files
        for library in libraries {
            let lib_src_dir = project_root.join(&library.path);

            for file in &library.files {
                let src = lib_src_dir.join(file);
                let dest = lib_dir.join(file);

                if !src.exists() {
                    println!(
                        "  Warning: {} not found at {}",
                        file.display(),
                        src.display()
                    );
                    continue;
                }

                if dest.exists() || dest.is_symlink() {
                    fs::remove_file(&dest).map_err(|e| SvmError::io(&dest, e))?;
                }

                if copy {
                    fs::copy(&src, &dest).map_err(|e| SvmError::io(&dest, e))?;
                    println!("  {} -> {} (copied)", file.display(), dest.display());
                } else {
                    #[cfg(unix)]
                    std::os::unix::fs::symlink(&src, &dest).map_err(|e| SvmError::io(&dest, e))?;

                    #[cfg(windows)]
                    std::os::windows::fs::symlink_file(&src, &dest)
                        .map_err(|e| SvmError::io(&dest, e))?;

                    println!("  {} -> {} (linked)", file.display(), src.display());
                }
            }
        }

        self.dirs.set_current(&version, &self.target)?;
        println!("\nDev mode active. Build with lake/cargo, binaries update automatically.");

        Ok(())
    }

    pub fn build_component(&self, component: &ComponentConfig, work_dir: &PathBuf) -> Result<()> {
        let parts: Vec<&str> = component.build_command.split_whitespace().collect();
        let (cmd, args) = parts.split_first().ok_or_else(|| SvmError::BuildFailed {
            component: component.name.clone(),
            message: "Empty build command".to_string(),
        })?;

        let status = Command::new(cmd)
            .args(args.iter())
            .current_dir(work_dir)
            .status()
            .map_err(|e| SvmError::BuildFailed {
                component: component.name.clone(),
                message: e.to_string(),
            })?;

        if !status.success() {
            return Err(SvmError::BuildFailed {
                component: component.name.clone(),
                message: format!("Command exited with status: {status}"),
            });
        }

        Ok(())
    }

    pub fn use_version(&self, version_str: &str) -> Result<()> {
        let version: Version = version_str
            .parse()
            .map_err(|e| SvmError::InvalidConfig(format!("Invalid version: {e}")))?;

        if !self.dirs.is_installed(&version, &self.target) {
            return Err(SvmError::VersionNotInstalled(version.to_string()));
        }

        self.dirs.set_current(&version, &self.target)?;
        println!("Now using Soma {version}");

        Ok(())
    }

    pub fn list(&self) -> Result<()> {
        let versions = self.dirs.installed_versions()?;
        let current = self.dirs.current_version(&self.target)?;

        if versions.is_empty() {
            println!("No versions installed.");
            println!("Run 'svm install --dev' to build from source.");
            return Ok(());
        }

        println!("Installed versions:");
        for version in versions {
            let marker = if Some(&version) == current.as_ref() {
                " (current)"
            } else {
                ""
            };

            let bin_dir = self.dirs.bin_dir(&version, &self.target);
            let components: Vec<&str> = ["somac", "haoma", "souls"]
                .into_iter()
                .filter(|c| bin_dir.join(c).exists())
                .collect();

            println!("  {}{}  [{}]", version, marker, components.join(", "));
        }

        Ok(())
    }

    pub fn current(&self) -> Result<()> {
        if let Some(version) = self.dirs.current_version(&self.target)? {
            println!("{version}");
            let bin_dir = self.dirs.current_bin_dir(&self.target);
            println!("Binary path: {}", bin_dir.display());
        } else {
            println!("No version currently active.");
            println!("Run 'svm use <version>' to activate a version.");
        }
        Ok(())
    }

    pub fn uninstall(&self, version_str: &str) -> Result<()> {
        let version: Version = version_str
            .parse()
            .map_err(|e| SvmError::InvalidConfig(format!("Invalid version: {e}")))?;

        if let Some(current) = self.dirs.current_version(&self.target)?
            && current == version
        {
            return Err(SvmError::CannotUninstallActive(version.to_string()));
        }

        self.dirs.remove_version(&version)?;
        println!("Uninstalled {version}");

        Ok(())
    }

    pub fn setup(&self, shell: Option<String>) -> Result<()> {
        let bin_path = self.dirs.current_bin_dir(&self.target);

        self.setup_system_env(&bin_path)?;

        self.setup_shell_env(shell, &bin_path)?;

        Ok(())
    }

    fn setup_system_env(&self, bin_path: &std::path::Path) -> Result<()> {
        #[cfg(target_os = "linux")]
        {
            self.setup_systemd_env(bin_path)?;
        }

        #[cfg(target_os = "macos")]
        {
            self.setup_macos_env(bin_path)?;
        }

        #[cfg(windows)]
        {
            self.setup_windows_env(bin_path)?;
        }

        Ok(())
    }

    #[cfg(windows)]
    fn setup_windows_env(&self, bin_path: &std::path::Path) -> Result<()> {
        use std::ptr;
        use winreg::RegKey;
        use winreg::enums::{HKEY_CURRENT_USER, KEY_READ, KEY_WRITE};

        let hkcu = RegKey::predef(HKEY_CURRENT_USER);
        let env = hkcu
            .open_subkey_with_flags("Environment", KEY_READ | KEY_WRITE)
            .map_err(|e| SvmError::ShellSetupFailed(format!("Failed to open registry: {e}")))?;

        let current_path: String = env.get_value("Path").unwrap_or_default();
        let bin_path_str = bin_path.to_string_lossy();

        if current_path
            .split(';')
            .any(|p| p.eq_ignore_ascii_case(&bin_path_str))
        {
            println!("PATH already contains {bin_path_str}");
            return Ok(());
        }

        let new_path = if current_path.is_empty() {
            bin_path_str.to_string()
        } else {
            format!("{bin_path_str};{current_path}")
        };

        env.set_value("Path", &new_path)
            .map_err(|e| SvmError::ShellSetupFailed(format!("Failed to update PATH: {e}")))?;

        let environment: Vec<u16> = "Environment\0".encode_utf16().collect();
        unsafe {
            SendMessageTimeoutW(
                HWND_BROADCAST,
                WM_SETTINGCHANGE,
                0,
                environment.as_ptr(),
                SMTO_ABORTIFHUNG,
                5000,
                ptr::null_mut(),
            );
        }

        println!("Added {bin_path_str} to user PATH");
        println!("Restart your terminal for changes to take effect.");

        Ok(())
    }

    #[cfg(target_os = "linux")]
    fn setup_systemd_env(&self, bin_path: &std::path::Path) -> Result<()> {
        use std::io::Write;

        let config_dir = dirs_path().join("environment.d");
        let config_file = config_dir.join("svm.conf");

        if config_file.exists() {
            let content =
                fs::read_to_string(&config_file).map_err(|e| SvmError::io(&config_file, e))?;
            if content.contains(".svm/current") {
                println!(
                    "System environment already configured in {}",
                    config_file.display()
                );
                return Ok(());
            }
        }

        fs::create_dir_all(&config_dir).map_err(|e| SvmError::io(&config_dir, e))?;

        let content = format!(
            "# Soma Version Manager\nPATH={}:$PATH\n",
            bin_path.display()
        );

        let mut file = fs::File::create(&config_file).map_err(|e| SvmError::io(&config_file, e))?;
        file.write_all(content.as_bytes())
            .map_err(|e| SvmError::io(&config_file, e))?;

        println!("Created {}", config_file.display());
        println!("  This configures PATH for GUI apps launched from your desktop environment.");
        println!("  Changes take effect on next login, or run:");
        println!("    systemctl --user import-environment PATH");

        Ok(())
    }

    #[cfg(target_os = "macos")]
    fn setup_macos_env(&self, bin_path: &std::path::Path) -> Result<()> {
        use std::io::Write;
        use std::process::Command;

        let base_dirs = BaseDirs::new().ok_or_else(|| {
            SvmError::ShellSetupFailed("Could not find home directory".to_string())
        })?;

        let launch_agents = base_dirs.home_dir().join("Library/LaunchAgents");
        let plist_file = launch_agents.join("com.soma.svm.plist");

        if plist_file.exists() {
            println!(
                "System environment already configured in {}",
                plist_file.display()
            );
            return Ok(());
        }

        fs::create_dir_all(&launch_agents).map_err(|e| SvmError::io(&launch_agents, e))?;

        let plist_content = format!(
            r#"<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>Label</key>
    <string>com.soma.svm</string>
    <key>ProgramArguments</key>
    <array>
        <string>/bin/launchctl</string>
        <string>setenv</string>
        <string>PATH</string>
        <string>{}:$PATH</string>
    </array>
    <key>RunAtLoad</key>
    <true/>
</dict>
</plist>
"#,
            bin_path.display()
        );

        let mut file = fs::File::create(&plist_file).map_err(|e| SvmError::io(&plist_file, e))?;
        file.write_all(plist_content.as_bytes())
            .map_err(|e| SvmError::io(&plist_file, e))?;

        println!("Created {}", plist_file.display());

        let bin_path_str = bin_path.to_string_lossy();
        let current_path = std::env::var("PATH").unwrap_or_default();
        let new_path = format!("{}:{}", bin_path_str, current_path);

        let status = Command::new("launchctl")
            .args(["setenv", "PATH", &new_path])
            .status();

        if status.map(|s| s.success()).unwrap_or(false) {
            println!("  PATH updated for current session.");
        }

        println!("  GUI apps will see the updated PATH after restart or re-login.");

        Ok(())
    }

    #[allow(dead_code)]
    fn setup_profile_fallback(&self, bin_path: &std::path::Path) -> Result<()> {
        use std::io::Write;

        let base_dirs = BaseDirs::new().ok_or_else(|| {
            SvmError::ShellSetupFailed("Could not find home directory".to_string())
        })?;

        let profile = base_dirs.home_dir().join(".profile");

        if profile.exists() {
            let content = fs::read_to_string(&profile).map_err(|e| SvmError::io(&profile, e))?;
            if content.contains(".svm/current") {
                println!(
                    "System environment already configured in {}",
                    profile.display()
                );
                return Ok(());
            }
        }

        let line = format!(
            "\n# Soma Version Manager\nexport PATH=\"{}:$PATH\"\n",
            bin_path.display()
        );

        let mut file = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&profile)
            .map_err(|e| SvmError::io(&profile, e))?;

        file.write_all(line.as_bytes())
            .map_err(|e| SvmError::io(&profile, e))?;

        println!("Added svm to PATH in {}", profile.display());

        Ok(())
    }

    fn setup_shell_env(&self, shell: Option<String>, bin_path: &std::path::Path) -> Result<()> {
        use std::io::Write;

        let shell = shell.unwrap_or_else(detect_shell);

        let base_dirs = BaseDirs::new().ok_or_else(|| {
            SvmError::ShellSetupFailed("Could not find home directory".to_string())
        })?;

        let home = base_dirs.home_dir();

        let (candidates, line_to_add) = match shell.as_str() {
            "bash" => (
                vec![home.join(".bashrc"), home.join(".bash_profile")],
                format!(
                    "\n# Soma Version Manager\nexport PATH=\"{}:$PATH\"\n",
                    bin_path.display()
                ),
            ),
            "zsh" => (
                vec![
                    home.join(".zshrc"),
                    home.join(".zshenv"),
                    home.join(".zprofile"),
                ],
                format!(
                    "\n# Soma Version Manager\nexport PATH=\"{}:$PATH\"\n",
                    bin_path.display()
                ),
            ),
            "fish" => (
                vec![base_dirs.config_dir().join("fish/config.fish")],
                format!(
                    "\n# Soma Version Manager\nset -gx PATH \"{}\" $PATH\n",
                    bin_path.display()
                ),
            ),
            "powershell" | "pwsh" => {
                let docs = base_dirs
                    .home_dir()
                    .join("Documents\\PowerShell\\Microsoft.PowerShell_profile.ps1");
                let docs_legacy = base_dirs
                    .home_dir()
                    .join("Documents\\WindowsPowerShell\\Microsoft.PowerShell_profile.ps1");
                (
                    vec![docs, docs_legacy],
                    format!(
                        "\n# Soma Version Manager\n$env:Path = \"{};$env:Path\"\n",
                        bin_path.display()
                    ),
                )
            }
            _ => {
                #[cfg(windows)]
                {
                    println!(
                        "Shell '{shell}' not supported, but PATH was added via Windows Registry."
                    );
                    return Ok(());
                }
                #[cfg(not(windows))]
                {
                    return Err(SvmError::ShellSetupFailed(format!(
                        "Unsupported shell: {}",
                        shell
                    )));
                }
            }
        };

        for candidate in &candidates {
            if candidate.exists()
                && let Ok(content) = fs::read_to_string(candidate)
                && content.contains(".svm/current")
            {
                println!("Shell already configured in {}", candidate.display());
                return Ok(());
            }
        }

        let mut last_error = None;
        for candidate in &candidates {
            let can_write = if candidate.exists() {
                if candidate.is_symlink() {
                    fs::OpenOptions::new().append(true).open(candidate).is_ok()
                } else {
                    fs::metadata(candidate)
                        .map(|m| !m.permissions().readonly())
                        .unwrap_or(false)
                }
            } else {
                candidate.parent().is_some_and(Path::exists)
            };

            if !can_write {
                last_error = Some(format!("{} is read-only", candidate.display()));
                continue;
            }

            match fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(candidate)
            {
                Ok(mut file) => {
                    file.write_all(line_to_add.as_bytes())
                        .map_err(|e| SvmError::io(candidate, e))?;

                    println!("Added svm to PATH in {}", candidate.display());
                    println!("Restart your shell or run: source {}", candidate.display());
                    return Ok(());
                }
                Err(e) => {
                    last_error = Some(format!("{}: {}", candidate.display(), e));
                }
            }
        }

        Err(SvmError::ShellSetupFailed(format!(
            "Could not write to any shell config file. Last error: {}",
            last_error.unwrap_or_else(|| "unknown".to_string())
        )))
    }
}

fn detect_shell() -> String {
    #[cfg(windows)]
    {
        if std::env::var("PSModulePath").is_ok() {
            return "powershell".to_string();
        }
        "powershell".to_string()
    }
    #[cfg(not(windows))]
    {
        std::env::var("SHELL")
            .ok()
            .and_then(|s| s.rsplit('/').next().map(|s| s.to_string()))
            .unwrap_or_else(|| "bash".to_string())
    }
}

pub fn self_uninstall(yes: bool) -> Result<()> {
    use std::io::{self, Write};

    let base_dirs = BaseDirs::new()
        .ok_or_else(|| SvmError::ShellSetupFailed("Could not find home directory".to_string()))?;

    let home = base_dirs.home_dir();
    let svm_dir = home.join(".svm");

    if !yes {
        println!("This will remove:");
        println!("  - {} (all installed versions)", svm_dir.display());
        println!("  - PATH entries from shell config files");
        println!("  - ~/.config/environment.d/svm.conf (if exists)");
        #[cfg(target_os = "macos")]
        println!("  - ~/Library/LaunchAgents/com.soma.svm.plist (if exists)");
        println!();
        print!("Are you sure? [y/N] ");
        io::stdout().flush().ok();

        let mut input = String::new();
        io::stdin().read_line(&mut input).ok();
        if !input.trim().eq_ignore_ascii_case("y") {
            println!("Aborted.");
            return Ok(());
        }
    }

    if svm_dir.exists() {
        fs::remove_dir_all(&svm_dir).map_err(|e| SvmError::io(&svm_dir, e))?;
        println!("Removed {}", svm_dir.display());
    }

    #[cfg(target_os = "linux")]
    {
        let env_file = dirs_path().join("environment.d/svm.conf");
        if env_file.exists() {
            fs::remove_file(&env_file).map_err(|e| SvmError::io(&env_file, e))?;
            println!("Removed {}", env_file.display());
        }
    }

    #[cfg(target_os = "macos")]
    {
        let plist_file = home.join("Library/LaunchAgents/com.soma.svm.plist");
        if plist_file.exists() {
            let _ = std::process::Command::new("launchctl")
                .args(["unload", &plist_file.to_string_lossy()])
                .status();
            fs::remove_file(&plist_file).map_err(|e| SvmError::io(&plist_file, e))?;
            println!("Removed {}", plist_file.display());
        }
    }

    let shell_files = [
        home.join(".bashrc"),
        home.join(".bash_profile"),
        home.join(".zshrc"),
        home.join(".zshenv"),
        home.join(".zprofile"),
        home.join(".profile"),
        base_dirs.config_dir().join("fish/config.fish"),
    ];

    for file in &shell_files {
        if file.exists()
            && !file.is_symlink()
            && let Ok(content) = fs::read_to_string(file)
            && (content.contains(".svm/current") || content.contains("Soma Version Manager"))
        {
            let new_content: String = content
                .lines()
                .filter(|line| {
                    !line.contains(".svm/current") && !line.contains("Soma Version Manager")
                })
                .collect::<Vec<_>>()
                .join("\n");

            if new_content.len() < content.len()
                && fs::write(file, new_content.trim_start_matches('\n')).is_ok()
            {
                println!("Cleaned {}", file.display());
            }
        }
    }

    println!();
    println!("svm has been uninstalled.");
    println!("You may need to restart your shell or log out and back in.");

    Ok(())
}
