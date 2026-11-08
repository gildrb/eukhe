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
use std::path::{Path, PathBuf};
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
        Err(error @ Failure::Usage(_)) => {
            eprintln!("usage: eukhe-next-version [--workspace-version X.Y.Z] < tags\n{error}");
            ExitCode::from(2)
        }
        Err(
            error @ (Failure::Workspace(_)
            | Failure::Stdin(_)
            | Failure::NoVersion(_)
            | Failure::NoSeriesStart(_)
            | Failure::Behind { .. }
            | Failure::Rule { .. }),
        ) => {
            eprintln!("error: {error}");
            ExitCode::from(1)
        }
    }
}

/// Why no release version prints: bad usage (exit 2), or no release (exit 1).
#[derive(Debug, thiserror::Error)]
enum Failure {
    #[error("unexpected arguments {0:?}")]
    Usage(Vec<String>),
    #[error(transparent)]
    Workspace(#[from] WorkspaceVersionError),
    #[error("cannot read the tags on stdin: {0}")]
    Stdin(#[source] std::io::Error),
    #[error("the workspace version {0:?} is not major.minor.patch")]
    NoVersion(String),
    #[error(
        "the workspace version {0} names no series start: it must be X.Y.0 (each release takes the next patch)"
    )]
    NoSeriesStart(String),
    #[error(
        "the next release {next} is not newer than the tag(s) {}: move the workspace version to a newer series",
        .newer.join(", ")
    )]
    Behind { next: String, newer: Vec<String> },
    #[error(
        "the release-version rule refused the workspace version {workspace:?} and the tags: {source}"
    )]
    Rule {
        workspace: String,
        #[source]
        source: eukhe_bend::Error,
    },
}

/// Why the manifest names no workspace version.
#[derive(Debug, thiserror::Error)]
enum WorkspaceVersionError {
    #[error("cannot read {}: {source}", .manifest.display())]
    Read {
        manifest: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("{} is not TOML: {source}", .manifest.display())]
    Parse {
        manifest: PathBuf,
        #[source]
        source: toml::de::Error,
    },
    #[error("{} has no [workspace.package] version", .manifest.display())]
    Missing { manifest: PathBuf },
}

fn run() -> Result<String, Failure> {
    let mut args = std::env::args().skip(1);
    let workspace = match (args.next(), args.next(), args.next()) {
        (None, None, None) => workspace_version(Path::new(MANIFEST))?,
        (Some(flag), Some(version), None) if flag == "--workspace-version" => version,
        (first, second, third) => {
            return Err(Failure::Usage(
                [first, second, third].into_iter().flatten().collect(),
            ));
        }
    };
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .map_err(Failure::Stdin)?;
    let tags: Vec<&str> = input.split('\n').filter(|line| !line.is_empty()).collect();
    match release(&workspace, &tags) {
        Ok(Release::Ready {
            version,
            tag,
            title,
        }) => Ok(format!("version={version}\ntag={tag}\ntitle={title}\n")),
        Ok(Release::NoVersion) => Err(Failure::NoVersion(workspace)),
        Ok(Release::NoSeriesStart) => Err(Failure::NoSeriesStart(workspace)),
        Ok(Release::Behind { next, newer }) => Err(Failure::Behind { next, newer }),
        Err(source) => Err(Failure::Rule { workspace, source }),
    }
}

/// `[workspace.package] version` of the manifest at `manifest`.
fn workspace_version(manifest: &Path) -> Result<String, WorkspaceVersionError> {
    let text = std::fs::read_to_string(manifest).map_err(|source| WorkspaceVersionError::Read {
        manifest: manifest.to_path_buf(),
        source,
    })?;
    let value: toml::Table = text
        .parse()
        .map_err(|source| WorkspaceVersionError::Parse {
            manifest: manifest.to_path_buf(),
            source,
        })?;
    value
        .get("workspace")
        .and_then(|workspace| workspace.get("package"))
        .and_then(|package| package.get("version"))
        .and_then(toml::Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| WorkspaceVersionError::Missing {
            manifest: manifest.to_path_buf(),
        })
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
        assert_eq!(
            read.map_err(|error| error.to_string()),
            Ok("0.10.0".to_string())
        );
    }
}
