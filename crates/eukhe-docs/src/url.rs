//! Internal URLs (docs/tools.md S7, `bend/tools.bend` §3): `scheme://path`
//! names something the session holds instead of a file under the working
//! directory. The path is a list of `/`-separated segments under the root
//! of its scheme: `..` goes up one, `.` and empty segments stay, and a path
//! that goes above its root is rejected, never clamped. A file-backed URL
//! also has a real-path guard the model does not need: its real path
//! (symlinks followed) must stay under the root's real path.

use std::path::PathBuf;

/// The schemes the `read` tool serves.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Scheme {
    /// `agent://<name|id>`: a subagent's chat.
    Agent,
    /// `skill://<name>/<path>`: a file under a skill's directory; the bare
    /// name is its `SKILL.md`.
    Skill,
    /// `memory://`, `memory://<id>`, `memory://<id>/<n>`: the chat memory's
    /// view, a message whole, a line.
    Memory,
    /// `mcp://<server>`, `mcp://<server>/<uri>`: an MCP server's resource
    /// listing, one resource. The `<uri>` is the server's, opaque: no
    /// segment walk.
    Mcp,
    /// `repo://<path>`: a file under the workspace root.
    Repo,
}

impl Scheme {
    /// Every scheme, in the order the messages name them.
    pub const ALL: [Self; 5] = [
        Self::Agent,
        Self::Skill,
        Self::Memory,
        Self::Mcp,
        Self::Repo,
    ];

    /// The scheme's name, without `://`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Agent => "agent",
            Self::Skill => "skill",
            Self::Memory => "memory",
            Self::Mcp => "mcp",
            Self::Repo => "repo",
        }
    }
}

/// Why an internal URL is not served; the message is model-facing.
#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum UrlError {
    /// The scheme is not one of [`Scheme::ALL`].
    #[error(
        "Unknown scheme {scheme}://; read serves agent://, skill://, memory://, mcp://, and repo://"
    )]
    UnknownScheme {
        /// Lowercase scheme without punctuation.
        scheme: String,
    },
    /// The path goes above the root of its scheme.
    #[error("{scheme}://{path} goes above the root of {scheme}://; `..` cannot leave it")]
    Escapes {
        /// The URL's scheme.
        scheme: &'static str,
        /// The rejected path, as written.
        path: String,
    },
    /// The path stays under its root as written, but its real path (a
    /// symlink followed) is outside the root's real path.
    #[error("{scheme}://{path} resolves outside the root of {scheme}:// through a symlink")]
    Leaves {
        /// The URL's scheme.
        scheme: &'static str,
        /// The rejected path, as written.
        path: String,
    },
}

/// Where a file-backed URL's names lead: the file or directory, and the
/// root its real path must stay under.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Located {
    pub root: PathBuf,
    pub path: PathBuf,
}

/// One segment of a URL path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Segment<'a> {
    /// A name: one level down.
    Name(&'a str),
    /// `..`: one level up.
    Up,
    /// `.` or an empty segment: no move.
    Here,
}

/// An internal URL: its scheme and its path as written.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Url<'a> {
    pub scheme: Scheme,
    pub path: &'a str,
}

impl<'a> Url<'a> {
    /// The URL `authored` names: `None` when it has no `scheme://`, an
    /// error when the scheme is not served.
    ///
    /// # Errors
    ///
    /// [`UrlError::UnknownScheme`].
    #[must_use]
    pub fn parse(authored: &'a str) -> Option<Result<Self, UrlError>> {
        let scheme = scheme_of(authored)?;
        let path = &authored[scheme.len() + "://".len()..];
        Some(
            Scheme::ALL
                .into_iter()
                .find(|known| known.name() == scheme)
                .map(|scheme| Url { scheme, path })
                .ok_or(UrlError::UnknownScheme { scheme }),
        )
    }

    /// The names under the root `path` reaches, root first.
    ///
    /// # Errors
    ///
    /// [`UrlError::Escapes`] when a `..` goes above the root.
    pub fn names(self) -> Result<Vec<&'a str>, UrlError> {
        let mut at = Vec::new();
        for segment in segments(self.path) {
            match segment {
                Segment::Name(name) => at.push(name),
                Segment::Here => {}
                Segment::Up => {
                    if at.pop().is_none() {
                        return Err(UrlError::Escapes {
                            scheme: self.scheme.name(),
                            path: self.path.to_owned(),
                        });
                    }
                }
            }
        }
        Ok(at)
    }
}

/// The segments of a URL path, in order.
pub(crate) fn segments(path: &str) -> impl Iterator<Item = Segment<'_>> {
    path.split('/').map(|segment| match segment {
        "" | "." => Segment::Here,
        ".." => Segment::Up,
        name => Segment::Name(name),
    })
}

/// The lowercase scheme of a `scheme://` input (RFC 3986 scheme syntax).
pub(crate) fn scheme_of(input: &str) -> Option<String> {
    let (scheme, _) = input.split_once("://")?;
    let mut bytes = scheme.bytes();
    let valid = bytes
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic())
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'+' | b'.' | b'-'));
    valid.then(|| scheme.to_ascii_lowercase())
}

#[cfg(test)]
mod bridge;

#[cfg(test)]
mod tests {
    use super::*;

    fn names(authored: &str) -> Option<Result<Vec<&str>, UrlError>> {
        Url::parse(authored).map(|url| url.and_then(Url::names))
    }

    #[test]
    fn parses_known_schemes_and_rejects_the_rest() {
        assert_eq!(
            [
                names("repo://src/./lib.rs"),
                names("REPO://a/b/../c"),
                names("memory://"),
                names("skill://s/../t/x.md"),
                names("ssh://host/etc"),
                names("src/a.rs"),
                names("C:/x"),
            ],
            [
                Some(Ok(vec!["src", "lib.rs"])),
                Some(Ok(vec!["a", "c"])),
                Some(Ok(vec![])),
                Some(Ok(vec!["t", "x.md"])),
                Some(Err(UrlError::UnknownScheme {
                    scheme: "ssh".to_owned()
                })),
                None,
                None,
            ]
        );
    }

    #[test]
    fn rejects_a_path_above_its_root() {
        assert_eq!(
            [
                names("repo://../x"),
                names("repo://a/../../x"),
                names("agent:///.."),
            ],
            [
                Some(Err(UrlError::Escapes {
                    scheme: "repo",
                    path: "../x".to_owned()
                })),
                Some(Err(UrlError::Escapes {
                    scheme: "repo",
                    path: "a/../../x".to_owned()
                })),
                Some(Err(UrlError::Escapes {
                    scheme: "agent",
                    path: "/..".to_owned()
                })),
            ]
        );
    }
}
