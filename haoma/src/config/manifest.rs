use std::collections::HashMap;

use kdl::{KdlDocument, KdlNode};
use miette::{Diagnostic, NamedSource, SourceSpan};
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub const MANIFEST_NAME: &str = "haoma.kdl";

#[derive(Error, Debug, Diagnostic)]
pub enum ManifestError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    ParseError(#[from] kdl::KdlError),

    #[error("Missing required field: '{field}'")]
    #[diagnostic(help("Add '{field} \"value\"' to your haoma.kdl"))]
    MissingField {
        field: String,
        #[source_code]
        src: NamedSource<String>,
    },

    #[error("Invalid value for '{field}': expected {expected}")]
    #[diagnostic()]
    InvalidValue {
        field: String,
        expected: String,
        #[source_code]
        src: NamedSource<String>,
        #[label("this value")]
        span: SourceSpan,
    },

    #[error("Invalid module type: '{value}'")]
    #[diagnostic(help("Use 'library' or 'binary'"))]
    InvalidModuleType {
        value: String,
        #[source_code]
        src: NamedSource<String>,
        #[label("invalid type")]
        span: SourceSpan,
    },

    #[error("Invalid dependency format for '{name}'")]
    #[diagnostic(help("Use: {name} path=\"../path\""))]
    InvalidDependency {
        name: String,
        #[source_code]
        src: NamedSource<String>,
        #[label("invalid dependency")]
        span: SourceSpan,
    },
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Manifest {
    pub name: String,
    pub version: String,
    pub module_type: ManifestModuleType,
    pub authors: Option<Vec<String>>,
    pub dependencies: ManifestDependencies,
}

impl Manifest {
    pub fn parse(source: &str, filename: &str) -> Result<Self, ManifestError> {
        let doc: KdlDocument = source.parse()?;
        let named_src = NamedSource::new(filename, source.to_string());

        let name = get_string_field(&doc, "name", &named_src)?;
        let version = get_string_field(&doc, "version", &named_src)?;
        let module_type = get_module_type(&doc, &named_src)?;
        let authors = get_string_list(&doc, "authors");
        let dependencies = get_dependencies(&doc, &named_src)?;

        Ok(Manifest {
            name,
            version,
            module_type,
            authors,
            dependencies,
        })
    }

    pub fn to_kdl(&self) -> String {
        let mut lines = Vec::new();

        lines.push(format!("name {:?}", self.name));
        lines.push(format!("version {:?}", self.version));
        lines.push(format!("type {:?}", self.module_type.as_str()));

        if let Some(authors) = &self.authors {
            if !authors.is_empty() {
                let author_args: Vec<String> = authors.iter().map(|a| format!("{:?}", a)).collect();
                lines.push(format!("authors {}", author_args.join(" ")));
            }
        }

        if !self.dependencies.dependencies.is_empty() {
            lines.push(String::new());
            lines.push("dependencies {".to_string());
            for (name, value) in &self.dependencies.dependencies {
                match value {
                    ManifestDependencyValue::Version(v) => {
                        lines.push(format!("    {} {:?}", name, v));
                    }
                    ManifestDependencyValue::Custom { path, version } => {
                        let mut dep_line = format!("    {} path={:?}", name, path);
                        if let Some(v) = version {
                            dep_line.push_str(&format!(" version={:?}", v));
                        }
                        lines.push(dep_line);
                    }
                }
            }
            lines.push("}".to_string());
        }

        lines.push(String::new());
        lines.join("\n")
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub enum ManifestModuleType {
    Library,
    Binary,
}

impl ManifestModuleType {
    pub fn as_str(&self) -> &'static str {
        match self {
            ManifestModuleType::Library => "library",
            ManifestModuleType::Binary => "binary",
        }
    }
}

#[derive(Serialize, Deserialize, Default, Debug, Clone)]
pub struct ManifestDependencies {
    pub dependencies: HashMap<String, ManifestDependencyValue>,
}

impl ManifestDependencies {
    pub fn new() -> Self {
        Self {
            dependencies: HashMap::new(),
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum ManifestDependencyValue {
    Version(String),
    Custom {
        path: String,
        version: Option<String>,
    },
}

fn get_string_field(
    doc: &KdlDocument,
    field: &str,
    src: &NamedSource<String>,
) -> Result<String, ManifestError> {
    let node = doc.get(field);

    let Some(node) = node else {
        return Err(ManifestError::MissingField {
            field: field.to_string(),
            src: src.clone(),
        });
    };

    let entry = node.entries().first();
    let Some(entry) = entry else {
        return Err(ManifestError::MissingField {
            field: field.to_string(),
            src: src.clone(),
        });
    };

    entry
        .value()
        .as_string()
        .map(|s| s.to_string())
        .ok_or_else(|| {
            let span = entry.span();
            ManifestError::InvalidValue {
                field: field.to_string(),
                expected: "string".to_string(),
                src: src.clone(),
                span: SourceSpan::new(span.offset().into(), span.len()),
            }
        })
}

fn get_module_type(
    doc: &KdlDocument,
    src: &NamedSource<String>,
) -> Result<ManifestModuleType, ManifestError> {
    let node = doc.get("type");

    let Some(node) = node else {
        return Err(ManifestError::MissingField {
            field: "type".to_string(),
            src: src.clone(),
        });
    };

    let entry = node.entries().first();
    let Some(entry) = entry else {
        return Err(ManifestError::MissingField {
            field: "type".to_string(),
            src: src.clone(),
        });
    };

    let span = entry.span();
    let source_span = SourceSpan::new(span.offset().into(), span.len());

    let Some(type_str) = entry.value().as_string() else {
        return Err(ManifestError::InvalidValue {
            field: "type".to_string(),
            expected: "string".to_string(),
            src: src.clone(),
            span: source_span,
        });
    };

    match type_str {
        "library" => Ok(ManifestModuleType::Library),
        "binary" => Ok(ManifestModuleType::Binary),
        other => Err(ManifestError::InvalidModuleType {
            value: other.to_string(),
            src: src.clone(),
            span: source_span,
        }),
    }
}

fn get_string_list(doc: &KdlDocument, field: &str) -> Option<Vec<String>> {
    doc.get(field).map(|node| {
        node.entries()
            .iter()
            .filter_map(|entry| entry.value().as_string().map(|s| s.to_string()))
            .collect()
    })
}

fn get_dependencies(
    doc: &KdlDocument,
    src: &NamedSource<String>,
) -> Result<ManifestDependencies, ManifestError> {
    let mut deps = ManifestDependencies::new();

    let Some(deps_node) = doc.get("dependencies") else {
        return Ok(deps);
    };

    let Some(children) = deps_node.children() else {
        return Ok(deps);
    };

    for node in children.nodes() {
        let dep = parse_dependency(node, src)?;
        deps.dependencies.insert(dep.0, dep.1);
    }

    Ok(deps)
}

fn parse_dependency(
    node: &KdlNode,
    src: &NamedSource<String>,
) -> Result<(String, ManifestDependencyValue), ManifestError> {
    let name = node.name().to_string();
    let node_span = node.span();

    // Check for path= property (Custom dependency)
    let path = node
        .get("path")
        .and_then(|e| e.as_string())
        .map(|s| s.to_string());

    if let Some(path) = path {
        let version = node
            .get("version")
            .and_then(|e| e.as_string())
            .map(|s| s.to_string());

        return Ok((name, ManifestDependencyValue::Custom { path, version }));
    }

    if let Some(entry) = node.entries().first() {
        if let Some(version) = entry.value().as_string() {
            return Ok((name, ManifestDependencyValue::Version(version.to_string())));
        }
    }

    Err(ManifestError::InvalidDependency {
        name,
        src: src.clone(),
        span: SourceSpan::new(node_span.offset().into(), node_span.len()),
    })
}
