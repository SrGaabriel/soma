use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Version {
    Dev,
    Semver(Semver),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Semver {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
    pub prerelease: Option<String>,
}

impl Version {
    pub fn dev() -> Self {
        Self::Dev
    }

    pub fn is_dev(&self) -> bool {
        matches!(self, Self::Dev)
    }

    pub fn as_str(&self) -> &str {
        match self {
            Self::Dev => "dev",
            Self::Semver(_) => panic!("Use Display for Semver"),
        }
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Dev => write!(f, "dev"),
            Self::Semver(v) => write!(f, "{}", v),
        }
    }
}

impl FromStr for Version {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "dev" {
            return Ok(Self::Dev);
        }
        s.parse::<Semver>().map(Self::Semver)
    }
}

impl fmt::Display for Semver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;
        if let Some(ref pre) = self.prerelease {
            write!(f, "-{}", pre)?;
        }
        Ok(())
    }
}

impl FromStr for Semver {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.strip_prefix('v').unwrap_or(s);
        let (version, prerelease) = match s.split_once('-') {
            Some((v, pre)) => (v, Some(pre.to_string())),
            None => (s, None),
        };

        let parts: Vec<&str> = version.split('.').collect();
        if parts.len() != 3 {
            return Err(format!("Invalid version format: {}", s));
        }

        Ok(Self {
            major: parts[0]
                .parse()
                .map_err(|_| format!("Invalid major version: {}", parts[0]))?,
            minor: parts[1]
                .parse()
                .map_err(|_| format!("Invalid minor version: {}", parts[1]))?,
            patch: parts[2]
                .parse()
                .map_err(|_| format!("Invalid patch version: {}", parts[2]))?,
            prerelease,
        })
    }
}

impl PartialOrd for Semver {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Semver {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.major.cmp(&other.major) {
            Ordering::Equal => {}
            ord => return ord,
        }
        match self.minor.cmp(&other.minor) {
            Ordering::Equal => {}
            ord => return ord,
        }
        match self.patch.cmp(&other.patch) {
            Ordering::Equal => {}
            ord => return ord,
        }
        match (&self.prerelease, &other.prerelease) {
            (None, None) => Ordering::Equal,
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (Some(a), Some(b)) => a.cmp(b),
        }
    }
}
