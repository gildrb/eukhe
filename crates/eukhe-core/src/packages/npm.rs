//! npm package operations: install/uninstall/version probes through the
//! configured npm command (`settings.npmCommand`, default `npm`), install
//! root/path layout per scope, and the project-root bootstrap files.
//!
//! npm user-scope packages install through `npm install -g` and resolve
//! against `npm root -g`; project-scope packages install into
//! `<cwd>/.eukhe/npm/node_modules` via `--prefix`.

use std::path::{Path, PathBuf};

use anyhow::{bail, Result};

use super::process::run_command_capture;
use super::source::{NpmSource, SourceScope};

/// The configured npm command (argv form) or plain `npm`.
pub fn npm_command(configured: Option<&[String]>) -> (&str, &[String]) {
    match configured.and_then(<[String]>::split_first) {
        Some((program, args)) => (program, args),
        None => ("npm", &[]),
    }
}

/// `prefix` then `rest` as one argv.
pub fn argv<'a>(prefix: &'a [String], rest: &[&'a str]) -> Vec<&'a str> {
    let mut argv = Vec::with_capacity(prefix.len() + rest.len());
    argv.extend(prefix.iter().map(String::as_str));
    argv.extend_from_slice(rest);
    argv
}

/// Dependency-install args for git packages: plain `install` when a custom
/// npm command is configured, `install --omit=dev` otherwise.
pub fn git_dependency_install_args(configured: Option<&[String]>) -> &'static [&'static str] {
    if configured.is_some_and(|command| !command.is_empty()) {
        &["install"]
    } else {
        &["install", "--omit=dev"]
    }
}

/// Ask npm for the global module root (`npm root -g`; bun uses its own
/// layout). The caller caches per npm-command identity.
pub fn discover_global_npm_root(command: &str, args: &[String]) -> Result<PathBuf> {
    if command == "bun" {
        let bin_dir =
            run_command_capture(command, &argv(args, &["pm", "bin", "-g"]), None, None, &[])?;
        let bin_dir = Path::new(bin_dir.trim());
        Ok(bin_dir
            .parent()
            .unwrap_or(bin_dir)
            .join("install")
            .join("global")
            .join("node_modules"))
    } else {
        let root = run_command_capture(command, &argv(args, &["root", "-g"]), None, None, &[])?;
        Ok(PathBuf::from(root.trim()))
    }
}

/// `npm view <name> version --json` (network probe).
pub fn latest_npm_version(command: &str, args: &[String], name: &str) -> Result<String> {
    let stdout = run_command_capture(
        command,
        &argv(args, &["view", name, "version", "--json"]),
        None,
        Some(std::time::Duration::from_millis(NETWORK_TIMEOUT_MS)),
        &[],
    )?;
    if stdout.trim().is_empty() {
        bail!("Empty response from npm view");
    }
    let version: serde_json::Value = serde_json::from_str(&stdout)
        .map_err(|error| anyhow::anyhow!("npm view returned invalid JSON: {error}"))?;
    Ok(version
        .as_str()
        .map_or_else(|| stdout.trim().to_string(), str::to_string))
}

/// Version recorded in an installed package's `package.json`.
pub fn installed_npm_version(installed_path: &Path) -> Option<String> {
    let content = std::fs::read_to_string(installed_path.join("package.json")).ok()?;
    let package: serde_json::Value = serde_json::from_str(&content).ok()?;
    package.get("version")?.as_str().map(str::to_string)
}

/// The 10s timeout used for npm/git network probes.
pub const NETWORK_TIMEOUT_MS: u64 = 10_000;

/// Directory the project-scope npm packages install into.
pub fn project_npm_root(cwd: &Path) -> PathBuf {
    cwd.join(super::CONFIG_DIR_NAME).join("npm")
}

/// Install root for npm packages in a scope (`temporary` uses the hash-stable
/// tmp layout; user installs target the global root's parent).
pub fn npm_install_root(scope: SourceScope, cwd: &Path, global_root: &Path) -> PathBuf {
    match scope {
        SourceScope::Temporary => super::temporary_dir("npm", None),
        SourceScope::Project => project_npm_root(cwd),
        SourceScope::User => global_root.parent().unwrap_or(global_root).to_path_buf(),
    }
}

/// Where an npm package is installed for a scope.
pub fn npm_install_path(
    source: &NpmSource,
    scope: SourceScope,
    cwd: &Path,
    global_root: &Path,
) -> PathBuf {
    match scope {
        SourceScope::Temporary => super::temporary_dir("npm", None)
            .join("node_modules")
            .join(&source.name),
        SourceScope::Project => project_npm_root(cwd)
            .join("node_modules")
            .join(&source.name),
        SourceScope::User => global_root.join(&source.name),
    }
}

/// Create the project npm root: directories, the self-excluding
/// `.gitignore`, and a minimal `package.json` when absent.
pub fn ensure_npm_project(install_root: &Path) -> Result<()> {
    std::fs::create_dir_all(install_root)?;
    ensure_gitignore(install_root)?;
    let package_json = install_root.join("package.json");
    if !package_json.exists() {
        let manifest = serde_json::json!({ "name": "pi-extensions", "private": true });
        std::fs::write(&package_json, serde_json::to_string_pretty(&manifest)?)?;
    }
    Ok(())
}

/// Write the self-excluding `.gitignore` when missing.
pub fn ensure_gitignore(dir: &Path) -> Result<()> {
    std::fs::create_dir_all(dir)?;
    let ignore_path = dir.join(".gitignore");
    if !ignore_path.exists() {
        std::fs::write(&ignore_path, "*\n!.gitignore\n")?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn npm_command_defaults_and_configuration() {
        let none: (&str, &[String]) = ("npm", &[]);
        assert_eq!(npm_command(None), none);
        assert_eq!(
            npm_command(Some(&["mise".to_owned(), "exec".to_owned()])),
            ("mise", &["exec".to_owned()][..])
        );
        assert_eq!(npm_command(Some(&[])), none);
    }

    #[test]
    fn git_dependency_args_follow_npm_command_configuration() {
        assert_eq!(git_dependency_install_args(None), ["install", "--omit=dev"]);
        assert_eq!(
            git_dependency_install_args(Some(&["bunx".to_owned(), "npm".to_owned()])),
            ["install"]
        );
    }

    #[test]
    fn install_paths_per_scope() {
        let cwd = Path::new("/work");
        let global_root = Path::new("/usr/lib/node_modules");
        let source = NpmSource {
            spec: "pkg".into(),
            name: "pkg".into(),
            pinned: false,
        };
        assert_eq!(
            npm_install_path(&source, SourceScope::User, cwd, global_root),
            PathBuf::from("/usr/lib/node_modules/pkg")
        );
        assert_eq!(
            npm_install_path(&source, SourceScope::Project, cwd, global_root),
            PathBuf::from("/work/.eukhe/npm/node_modules/pkg")
        );
        assert_eq!(
            npm_install_root(SourceScope::User, cwd, global_root),
            PathBuf::from("/usr/lib")
        );
    }

    #[test]
    fn reads_installed_version() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("package.json"),
            r#"{"name":"pkg","version":"1.2.3"}"#,
        )
        .unwrap();
        assert_eq!(installed_npm_version(dir.path()).as_deref(), Some("1.2.3"));
        assert_eq!(installed_npm_version(&dir.path().join("missing")), None);
    }
}
