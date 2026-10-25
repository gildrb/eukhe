//! Package source parsing: `npm:` specs, git URLs, and local paths, plus the
//! path-resolution helpers the package manager uses to bind sources to
//! install locations and settings entries.
//!
//! Behavior contract (user-visible strings included):
//! - `npm:<spec>` is always an npm source; the spec may pin a version
//!   (`npm:@scope/pkg@1.2.3`), which disables auto-updates.
//! - Local sources are anything that is not an `npm:`/`git:`/URL protocol
//!   prefix, including bare relative paths.
//! - Git sources are explicit protocol URLs (`https://`, `http://`, `ssh://`,
//!   `git://`) or - with the `git:` prefix - host/path shorthand and
//!   scp-like forms. `git://` URLs are *not* git sources: the `git:` prefix
//!   is stripped first, so `git://host/path` parses as a local path. This
//!   quirk is product behavior, not a bug to fix here.
//!
//! Every source decision and text is the compiled core's
//! (`eukhe_bend::rules::package_source`, `laws/package_source.bend`); the
//! path helpers over `std::path` stay here.

use std::path::{Path, PathBuf};

use eukhe_bend::rules::package_source as rules;

/// Scope a package source belongs to: user settings, project settings, or an
/// ephemeral resolve-only scope (temporary sources are never persisted).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SourceScope {
    User,
    Project,
    Temporary,
}

/// Persisted settings scope for package sources.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UserOrProject {
    User,
    Project,
}

impl UserOrProject {
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            UserOrProject::User => "user",
            UserOrProject::Project => "project",
        }
    }
}

impl From<UserOrProject> for SourceScope {
    fn from(scope: UserOrProject) -> Self {
        match scope {
            UserOrProject::User => SourceScope::User,
            UserOrProject::Project => SourceScope::Project,
        }
    }
}

/// A parsed `npm:` source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NpmSource {
    /// The spec with the `npm:` prefix removed (`@scope/pkg@1.2.3`).
    pub spec: String,
    pub name: String,
    /// True when the spec pins a version; pinned packages never auto-update.
    pub pinned: bool,
}

/// A parsed git source (subset of the hosted-git-info forms; the generic
/// fallback covers every host containing a dot or `localhost`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GitSource {
    /// Clone URL, always valid for `git clone` (no ref suffix).
    pub repo: String,
    /// Git host domain (`github.com`).
    pub host: String,
    /// Repository path (`user/repo`).
    pub path: String,
    /// Optional ref (branch, tag, or commit).
    pub r#ref: Option<String>,
    /// True when a ref was specified; pinned packages never auto-update.
    pub pinned: bool,
}

/// A local filesystem source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalSource {
    pub path: String,
}

/// The parsed form of a package source string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParsedSource {
    Npm(NpmSource),
    Git(GitSource),
    Local(LocalSource),
}

/// The part of a package source a [`SourceParseError`] rejects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourcePart {
    GitHost,
    GitPath,
    GitRef,
    CloneUrl,
    NpmSpec,
    NpmName,
}

impl From<SourcePart> for rules::Part {
    fn from(part: SourcePart) -> Self {
        match part {
            SourcePart::GitHost => rules::Part::GitHost,
            SourcePart::GitPath => rules::Part::GitPath,
            SourcePart::GitRef => rules::Part::GitRef,
            SourcePart::CloneUrl => rules::Part::CloneUrl,
            SourcePart::NpmSpec => rules::Part::NpmSpec,
            SourcePart::NpmName => rules::Part::NpmName,
        }
    }
}

impl From<rules::Part> for SourcePart {
    fn from(part: rules::Part) -> Self {
        match part {
            rules::Part::GitHost => SourcePart::GitHost,
            rules::Part::GitPath => SourcePart::GitPath,
            rules::Part::GitRef => SourcePart::GitRef,
            rules::Part::CloneUrl => SourcePart::CloneUrl,
            rules::Part::NpmSpec => SourcePart::NpmSpec,
            rules::Part::NpmName => SourcePart::NpmName,
        }
    }
}

impl std::fmt::Display for SourcePart {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&rules::part_text((*self).into()))
    }
}

/// Why a source part is unsafe to hand to git/npm or to join onto an install
/// root.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceDefect {
    Empty,
    EmptySegment,
    DotSegment,
    DrivePrefix,
    Backslash,
    ControlCharacter,
    LeadingDash,
    Slash,
}

impl From<SourceDefect> for rules::Defect {
    fn from(defect: SourceDefect) -> Self {
        match defect {
            SourceDefect::Empty => rules::Defect::Empty,
            SourceDefect::EmptySegment => rules::Defect::EmptySegment,
            SourceDefect::DotSegment => rules::Defect::DotSegment,
            SourceDefect::DrivePrefix => rules::Defect::DrivePrefix,
            SourceDefect::Backslash => rules::Defect::Backslash,
            SourceDefect::ControlCharacter => rules::Defect::ControlCharacter,
            SourceDefect::LeadingDash => rules::Defect::LeadingDash,
            SourceDefect::Slash => rules::Defect::Slash,
        }
    }
}

impl From<rules::Defect> for SourceDefect {
    fn from(defect: rules::Defect) -> Self {
        match defect {
            rules::Defect::Empty => SourceDefect::Empty,
            rules::Defect::EmptySegment => SourceDefect::EmptySegment,
            rules::Defect::DotSegment => SourceDefect::DotSegment,
            rules::Defect::DrivePrefix => SourceDefect::DrivePrefix,
            rules::Defect::Backslash => SourceDefect::Backslash,
            rules::Defect::ControlCharacter => SourceDefect::ControlCharacter,
            rules::Defect::LeadingDash => SourceDefect::LeadingDash,
            rules::Defect::Slash => SourceDefect::Slash,
        }
    }
}

impl std::fmt::Display for SourceDefect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&rules::defect_text((*self).into()))
    }
}

/// A package source that has a recognized npm/git shape but carries a part
/// that could escape the install root or be read as a command-line option.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceParseError {
    pub input: String,
    pub part: SourcePart,
    pub defect: SourceDefect,
}

impl std::fmt::Display for SourceParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&rules::error_text(
            &self.input,
            rules::Flaw {
                part: self.part.into(),
                defect: self.defect.into(),
            },
        ))
    }
}

impl std::error::Error for SourceParseError {}

fn rejection(input: &str, flaw: rules::Flaw) -> SourceParseError {
    SourceParseError {
        input: input.to_string(),
        part: flaw.part.into(),
        defect: flaw.defect.into(),
    }
}

impl From<rules::Git> for GitSource {
    fn from(git: rules::Git) -> Self {
        GitSource {
            repo: git.repo,
            host: git.host,
            path: git.path,
            r#ref: git.r#ref,
            pinned: git.pinned,
        }
    }
}

/// Parse a package source into a git source.
///
/// Rules: with the `git:` prefix every historical shorthand form is accepted;
/// without it only explicit protocol URLs parse as git. `Ok(None)` means the
/// source has no git shape; a git-shaped source whose host, path, ref, or
/// clone URL could escape the install root or act as a git option is an
/// error.
///
/// # Errors
///
/// Returns a [`SourceParseError`] naming the rejected part.
pub fn parse_git_url(source: &str) -> Result<Option<GitSource>, SourceParseError> {
    rules::git(source)
        .map(|git| git.map(GitSource::from))
        .map_err(|flaw| rejection(source, flaw))
}

/// Parse an npm spec into name and optional pinned version.
pub fn parse_npm_spec(spec: &str) -> (String, Option<String>) {
    rules::npm_spec(spec)
}

/// Parse a raw package source string.
///
/// # Errors
///
/// Returns a [`SourceParseError`] when an `npm:` spec or a git-shaped source
/// carries a part that could escape its install root or be read as a
/// command-line option; such sources never fall back to another kind.
pub fn parse_source(source: &str) -> Result<ParsedSource, SourceParseError> {
    Ok(
        match rules::source(source).map_err(|flaw| rejection(source, flaw))? {
            rules::Source::Npm(npm) => ParsedSource::Npm(NpmSource {
                spec: npm.spec,
                name: npm.name,
                pinned: npm.pinned,
            }),
            rules::Source::Git(git) => ParsedSource::Git(git.into()),
            rules::Source::Local(path) => ParsedSource::Local(LocalSource { path }),
        },
    )
}

/// Lexical absolutization (node `path.resolve`): joins onto the base and
/// collapses `.`/`..` without touching the filesystem.
pub fn lexical_resolve(base: &Path, input: &str) -> PathBuf {
    eukhe_docs::lexical_normalize(&base.join(input))
}

/// node `path.relative` over pre-resolved absolute paths.
pub fn path_relative(from: &Path, to: &Path) -> String {
    let from: Vec<_> = from.components().collect();
    let to: Vec<_> = to.components().collect();
    let mut shared = 0;
    while shared < from.len() && shared < to.len() && from[shared] == to[shared] {
        shared += 1;
    }
    let mut segments: Vec<String> = Vec::new();
    for _ in shared..from.len() {
        segments.push("..".to_string());
    }
    for component in &to[shared..] {
        segments.push(component.as_os_str().to_string_lossy().into_owned());
    }
    segments.join("/")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolves_paths_lexically() {
        let base = Path::new("/work/project");
        assert_eq!(
            lexical_resolve(base, "sub/pkg"),
            PathBuf::from("/work/project/sub/pkg")
        );
        assert_eq!(lexical_resolve(base, "../x"), PathBuf::from("/work/x"));
        assert_eq!(lexical_resolve(base, "/abs"), PathBuf::from("/abs"));
        assert_eq!(path_relative(base, Path::new("/work")), "..");
        assert_eq!(path_relative(base, base), "");
    }

    fn rejected(input: &str, part: SourcePart, defect: SourceDefect) -> SourceParseError {
        SourceParseError {
            input: input.to_string(),
            part,
            defect,
        }
    }

    /// End to end through the core and the Rust type mapping (every part,
    /// every defect but `Empty`, and the error text).
    #[test]
    fn rejects_sources_that_escape_the_install_root_or_read_as_options() {
        let cases = [
            (
                "git:git@h.io:../../../../tmp/a/b",
                SourcePart::GitPath,
                SourceDefect::DotSegment,
            ),
            (
                "git:git@/home/u:x/y",
                SourcePart::GitHost,
                SourceDefect::Slash,
            ),
            (
                "git:github:../x",
                SourcePart::GitPath,
                SourceDefect::DotSegment,
            ),
            (
                "git:../../x/y",
                SourcePart::GitHost,
                SourceDefect::DotSegment,
            ),
            (
                "git:github.com/user//repo",
                SourcePart::GitPath,
                SourceDefect::EmptySegment,
            ),
            (
                "git:git@h.io:user\\..\\x/y",
                SourcePart::GitPath,
                SourceDefect::Backslash,
            ),
            (
                "git:git@h.io:C:/x",
                SourcePart::GitPath,
                SourceDefect::DrivePrefix,
            ),
            (
                "git:git@h.io:user/repo\u{0}",
                SourcePart::GitPath,
                SourceDefect::ControlCharacter,
            ),
            (
                "git:git@-oProxyCommand=x.io:user/repo",
                SourcePart::GitHost,
                SourceDefect::LeadingDash,
            ),
            (
                "git:github.com/user/repo@--orphan=x",
                SourcePart::GitRef,
                SourceDefect::LeadingDash,
            ),
            (
                "https://github.com/user/repo@-x",
                SourcePart::GitRef,
                SourceDefect::LeadingDash,
            ),
            (
                "ssh://-oProxyCommand=x@h.io/user/repo",
                SourcePart::CloneUrl,
                SourceDefect::LeadingDash,
            ),
            (
                "npm:--registry=http://evil.test",
                SourcePart::NpmSpec,
                SourceDefect::LeadingDash,
            ),
            ("npm:../../x", SourcePart::NpmName, SourceDefect::DotSegment),
        ];
        for (input, part, defect) in cases {
            assert_eq!(
                parse_source(input),
                Err(rejected(input, part, defect)),
                "{input}"
            );
        }
        assert_eq!(
            rejected("npm:", SourcePart::NpmSpec, SourceDefect::Empty).to_string(),
            "Invalid package source npm:: npm spec is empty"
        );
    }

    /// End to end through the core and the Rust type mapping of a git source.
    #[test]
    fn keeps_safe_refs_on_git_sources() {
        assert_eq!(
            parse_source("git:github.com/user/repo@v1"),
            Ok(ParsedSource::Git(GitSource {
                repo: "https://github.com/user/repo".to_string(),
                host: "github.com".to_string(),
                path: "user/repo".to_string(),
                r#ref: Some("v1".to_string()),
                pinned: true,
            }))
        );
    }
}
