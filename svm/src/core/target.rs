use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Target {
    pub arch: String,
    pub vendor: Option<String>,
    pub os: String,
    pub env: Option<String>,
}

impl Target {
    pub fn host() -> Self {
        Self {
            arch: std::env::consts::ARCH.to_string(),
            vendor: Self::detect_vendor(),
            os: std::env::consts::OS.to_string(),
            env: Self::detect_env(),
        }
    }

    fn detect_vendor() -> Option<String> {
        match std::env::consts::OS {
            "macos" | "ios" => Some("apple".to_string()),
            "linux" => Some("unknown".to_string()),
            "windows" => Some("pc".to_string()),
            _ => None,
        }
    }

    fn detect_env() -> Option<String> {
        #[cfg(target_env = "gnu")]
        return Some("gnu".to_string());

        #[cfg(target_env = "musl")]
        return Some("musl".to_string());

        #[cfg(target_env = "msvc")]
        return Some("msvc".to_string());

        #[cfg(not(any(target_env = "gnu", target_env = "musl", target_env = "msvc")))]
        None
    }
}

impl fmt::Display for Target {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.arch)?;
        if let Some(ref vendor) = self.vendor {
            write!(f, "-{vendor}")?;
        }
        write!(f, "-{}", self.os)?;
        if let Some(ref env) = self.env {
            write!(f, "-{env}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_host_detection() {
        let host = Target::host();
        assert!(!host.arch.is_empty());
        assert!(!host.os.is_empty());
    }
}
