//! `eukhe-next-version`: the version of the next eukhe release.
//!
//! Usage: `eukhe-next-version [--workspace-version X.Y.Z] < tags`
//!
//! Reads the repository's tag names on stdin, one per line, and prints the
//! release's version, tag and title as `key=value` lines (`GITHUB_OUTPUT`
//! format):
//!
//! ```text
//! version=0.10.4
//! tag=eukhe-v0.10.4
//! title=Eukhe v0.10.4
//! ```
//!
//! The series is the workspace version of Cargo.toml (`[workspace.package]`
//! version) unless `--workspace-version` names one. The rule (the next
//! patch of the series, newer than every version tag) runs as its compiled
//! Bend model (`eukhe_bend::rules::semver::release`; `bend/semver.bend`,
//! laws `laws/semver.bend`): this program only reads and prints. A commit
//! with no release prints why on stderr and exits 1; bad usage exits 2.

use std::io::Read;
use std::path::Path;
use std::process::ExitCode;

use eukhe_bend::rules::semver::{release, Release};

/// The workspace manifest, relative to this crate.
const MANIFEST: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../Cargo.toml");

fn main() -> ExitCode {
    match run() {
        Ok(lines) => {
            print!("{lines}");
            ExitCode::SUCCESS
        }
        Err(Failure::Usage(message)) => {
            eprintln!("usage: eukhe-next-version [--workspace-version X.Y.Z] < tags\n{message}");
            ExitCode::from(2)
        }
        Err(Failure::NoRelease(message)) => {
            eprintln!("error: {message}");
            ExitCode::from(1)
        }
    }
}

enum Failure {
    Usage(String),
    NoRelease(String),
}

fn run() -> Result<String, Failure> {
    let mut args = std::env::args().skip(1);
    let workspace = match (args.next(), args.next(), args.next()) {
        (None, None, None) => workspace_version(Path::new(MANIFEST)).map_err(Failure::NoRelease)?,
        (Some(flag), Some(version), None) if flag == "--workspace-version" => version,
        (first, second, third) => {
            let given: Vec<String> = [first, second, third].into_iter().flatten().collect();
            return Err(Failure::Usage(format!("unexpected arguments {given:?}")));
        }
    };
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .map_err(|error| Failure::NoRelease(format!("cannot read the tags on stdin: {error}")))?;
    let tags: Vec<&str> = input.split('\n').filter(|line| !line.is_empty()).collect();
    match release(&workspace, &tags) {
        Ok(Release::Ready {
            version,
            tag,
            title,
        }) => Ok(format!("version={version}\ntag={tag}\ntitle={title}\n")),
        Ok(Release::NoVersion) => Err(Failure::NoRelease(format!(
            "the workspace version {workspace:?} is not major.minor.patch"
        ))),
        Ok(Release::NoSeriesStart) => Err(Failure::NoRelease(format!(
            "the workspace version {workspace} names no series start: it must be X.Y.0 (each release takes the next patch)"
        ))),
        Ok(Release::Behind { next, newer }) => Err(Failure::NoRelease(format!(
            "the next release {next} is not newer than the tag(s) {}: move the workspace version to a newer series",
            newer.join(", ")
        ))),
        Err(error) => Err(Failure::NoRelease(format!(
            "the release-version rule refused the workspace version {workspace:?} and the tags: {error}"
        ))),
    }
}

/// `[workspace.package] version` of the manifest at `manifest`.
fn workspace_version(manifest: &Path) -> Result<String, String> {
    let text = std::fs::read_to_string(manifest)
        .map_err(|error| format!("cannot read {}: {error}", manifest.display()))?;
    let value: toml::Table = text
        .parse()
        .map_err(|error| format!("{} is not TOML: {error}", manifest.display()))?;
    value
        .get("workspace")
        .and_then(|workspace| workspace.get("package"))
        .and_then(|package| package.get("version"))
        .and_then(toml::Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| format!("{} has no [workspace.package] version", manifest.display()))
}

#[cfg(test)]
mod tests {
    use super::workspace_version;

    #[test]
    fn the_workspace_version_is_read_from_cargo_toml() {
        let dir = std::env::temp_dir().join(format!("eukhe-next-version-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let manifest = dir.join("Cargo.toml");
        std::fs::write(
            &manifest,
            "[package]\nversion = \"9.9.9\"\n\n[workspace.package]\nversion = \"0.10.0\"\n",
        )
        .unwrap();
        let read = workspace_version(&manifest);
        std::fs::remove_dir_all(&dir).unwrap();
        assert_eq!(read, Ok("0.10.0".to_string()));
    }
}
