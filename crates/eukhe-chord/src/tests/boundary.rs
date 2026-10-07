//! Port of `test/boundary.test.ts`.
//!
//! The Rust package boundary: the manifest declares no `eukhe-*` workspace
//! crate (the TS check rejects `@earendil-works/pi-*` dependencies), and no
//! source file reaches outside `src/` through a module path attribute or an
//! include macro (the TS check rejects relative imports leaving `src/`).

use std::fs;
use std::path::{Component, Path, PathBuf};

/// Dependency names of every `*dependencies` table in a Cargo manifest.
fn dependency_names(manifest: &str) -> Vec<String> {
    let mut names = Vec::new();
    let mut in_dependencies = false;
    for line in manifest.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(header) = line.strip_prefix('[') {
            let header = header.trim_start_matches('[').trim_end_matches(']').trim();
            in_dependencies = header.ends_with("dependencies");
            if let Some((table, name)) = header.rsplit_once('.') {
                if table.ends_with("dependencies") {
                    names.push(name.trim_matches('"').to_owned());
                }
            }
            continue;
        }
        if in_dependencies {
            if let Some((key, _)) = line.split_once('=') {
                let name = key.split('.').next().unwrap_or(key).trim();
                names.push(name.trim_matches('"').to_owned());
            }
        }
    }
    names
}

fn rust_files(directory: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            rust_files(&path, files);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            files.push(path);
        }
    }
}

/// Lexically resolve `relative` against `base` (`path.resolve`).
fn resolve(base: &Path, relative: &str) -> PathBuf {
    let mut resolved = PathBuf::new();
    for component in base.join(relative).components() {
        match component {
            Component::ParentDir => {
                resolved.pop();
            }
            Component::CurDir => {}
            Component::Prefix(_) | Component::RootDir | Component::Normal(_) => {
                resolved.push(component.as_os_str());
            }
        }
    }
    resolved
}

/// The first string literal at the start of `text` (after whitespace).
fn string_literal(text: &str) -> Option<&str> {
    let rest = text.trim_start().strip_prefix('"')?;
    rest.split_once('"').map(|(literal, _)| literal)
}

/// Relative paths a source file names through `#[path = "..."]` or
/// `include!("...")` / `include_str!("...")` / `include_bytes!("...")`.
fn referenced_paths(source: &str) -> Vec<&str> {
    // Built with `concat!` so this file does not match its own needles.
    let path_attribute = concat!("#[", "path");
    let includes = [
        concat!("include", "!("),
        concat!("include", "_str!("),
        concat!("include", "_bytes!("),
    ];
    let mut paths = Vec::new();
    for (at, _) in source.match_indices(path_attribute) {
        let rest = source[at + path_attribute.len()..].trim_start();
        if let Some(literal) = rest.strip_prefix('=').and_then(string_literal) {
            paths.push(literal);
        }
    }
    for needle in includes {
        for (at, _) in source.match_indices(needle) {
            if let Some(literal) = string_literal(&source[at + needle.len()..]) {
                paths.push(literal);
            }
        }
    }
    paths
}

#[test]
fn does_not_depend_on_pi_packages_or_files_outside_chord() {
    let package_directory = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source_directory = package_directory.join("src");
    let manifest = fs::read_to_string(package_directory.join("Cargo.toml")).unwrap();
    let workspace_dependencies: Vec<String> = dependency_names(&manifest)
        .into_iter()
        .filter(|name| name.starts_with("eukhe-") || name.starts_with("eukhe_"))
        .collect();
    assert_eq!(workspace_dependencies, Vec::<String>::new());

    let mut paths = Vec::new();
    rust_files(&source_directory, &mut paths);
    paths.sort();
    let mut violations = Vec::new();
    for file in &paths {
        let source = fs::read_to_string(file).unwrap();
        let directory = file.parent().unwrap();
        for specifier in referenced_paths(&source) {
            if !resolve(directory, specifier).starts_with(&source_directory) {
                let relative = file.strip_prefix(&source_directory).unwrap().display();
                violations.push(format!("{relative}: {specifier}"));
            }
        }
    }
    assert_eq!(violations, Vec::<String>::new());
}

#[test]
fn detects_dependencies_and_escaping_paths() {
    let manifest = "[dependencies]\nfutures.workspace = true\neukhe-types = { path = \"../x\" }\n\
                    [dev-dependencies.eukhe-core]\npath = \"../y\"\n[lints]\nworkspace = true\n";
    assert_eq!(
        dependency_names(manifest),
        vec!["futures", "eukhe-types", "eukhe-core"]
    );
    let source = concat!(
        "#[",
        "path = \"../outside.rs\"]\nmod outside;\n",
        "include",
        "_str!(\"inner.txt\")"
    );
    assert_eq!(referenced_paths(source), vec!["../outside.rs", "inner.txt"]);
    assert!(!resolve(Path::new("/crate/src/tests"), "../../outside.rs").starts_with("/crate/src"));
    assert!(resolve(Path::new("/crate/src/tests"), "../inner.rs").starts_with("/crate/src"));
}
