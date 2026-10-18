//! Internal URLs (docs/tools.md S7, `bend/tools.bend` §3): `scheme://path`
//! names something the session holds instead of a file under the working
//! directory. The path is a list of `/`-separated segments under the root
//! of its scheme: `..` goes up one, `.` and empty segments stay, and a path
//! that goes above its root is rejected, never clamped. A file-backed URL
//! also has a real-path guard the model does not need: its real path
//! (symlinks followed) must stay under the root's real path. An `ssh://`
//! path has one of two roots on its host: the remote `/`, or the remote
//! home when its first segment is `~` ([`Url::remote`]).

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
    /// `ssh://<host>/<path>`: a file on a host the user allows, read
    /// through the user's own `ssh` ([`Url::remote`]).
    Ssh,
}

impl Scheme {
    /// Every scheme, in the order the messages name them.
    pub const ALL: [Self; 6] = [
        Self::Agent,
        Self::Skill,
        Self::Memory,
        Self::Mcp,
        Self::Repo,
        Self::Ssh,
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
            Self::Ssh => "ssh",
        }
    }
}

/// Why an internal URL is not served; the message is model-facing.
#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum UrlError {
    /// The scheme is not one of [`Scheme::ALL`].
    #[error(
        "Unknown scheme {scheme}://; read serves agent://, skill://, memory://, mcp://, repo://, and ssh://"
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
    /// The host of an `ssh://` URL is not a plain host name: empty, a
    /// leading `-` (an `ssh` option), or a character other than a letter,
    /// a digit, `.`, `-`, `_` and `@`.
    #[error(
        "ssh://{host}/ does not name a host; write ssh://<host>/<path> with a host of letters, digits, `.`, `-`, `_` and `@` (set ports and options in ~/.ssh/config)"
    )]
    Host {
        /// The rejected host, as written.
        host: String,
    },
}

/// Where a file-backed URL's names lead: the file or directory, and the
/// root its real path must stay under.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Located {
    pub root: PathBuf,
    pub path: PathBuf,
}

/// Where an `ssh://` URL's names lead on the remote host.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Remote<'a> {
    /// The host as written (`box`, `user@box`).
    pub host: &'a str,
    /// The path the remote read gets: absolute (`/etc/hosts`), or relative
    /// to the remote home (`notes/a.md`; `.` for the home).
    pub path: String,
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
        walk(self.path).ok_or_else(|| self.escapes())
    }

    /// The host and remote path of an `ssh://<host>/<path>` URL. The path
    /// is walked like every URL path. Its root is the remote `/`; when its
    /// first segment is `~`, the root is the remote home and the path is
    /// relative to it.
    ///
    /// # Errors
    ///
    /// [`UrlError::Host`] when the host is not a plain host name;
    /// [`UrlError::Escapes`] when a `..` goes above the root.
    pub fn remote(self) -> Result<Remote<'a>, UrlError> {
        let (host, rest) = self.path.split_once('/').unwrap_or((self.path, ""));
        let plain = !host.is_empty()
            && !host.starts_with('-')
            && host.bytes().all(|byte| {
                byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'_' | b'@')
            });
        if !plain {
            return Err(UrlError::Host {
                host: host.to_owned(),
            });
        }
        let home = rest
            .strip_prefix('~')
            .filter(|under| under.is_empty() || under.starts_with('/'));
        let path = match home {
            Some(under) => {
                let names = walk(under).ok_or_else(|| self.escapes())?;
                if names.is_empty() {
                    ".".to_owned()
                } else {
                    names.join("/")
                }
            }
            None => format!("/{}", walk(rest).ok_or_else(|| self.escapes())?.join("/")),
        };
        Ok(Remote { host, path })
    }

    fn escapes(self) -> UrlError {
        UrlError::Escapes {
            scheme: self.scheme.name(),
            path: self.path.to_owned(),
        }
    }
}

/// The names `path` reaches under its root, root first; `None` when a
/// `..` goes above the root.
fn walk(path: &str) -> Option<Vec<&str>> {
    let mut at = Vec::new();
    for segment in segments(path) {
        match segment {
            Segment::Name(name) => at.push(name),
            Segment::Here => {}
            Segment::Up => {
                at.pop()?;
            }
        }
    }
    Some(at)
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
                names("sftp://host/etc"),
                names("src/a.rs"),
                names("C:/x"),
            ],
            [
                Some(Ok(vec!["src", "lib.rs"])),
                Some(Ok(vec!["a", "c"])),
                Some(Ok(vec![])),
                Some(Ok(vec!["t", "x.md"])),
                Some(Err(UrlError::UnknownScheme {
                    scheme: "sftp".to_owned()
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

    fn remote(authored: &str) -> Result<Remote<'_>, UrlError> {
        Url::parse(authored).expect("a URL").and_then(Url::remote)
    }

    fn at<'a>(host: &'a str, path: &str) -> Remote<'a> {
        Remote {
            host,
            path: path.to_owned(),
        }
    }

    #[test]
    fn an_ssh_url_names_a_host_and_a_path_under_slash_or_the_home() {
        assert_eq!(
            [
                remote("ssh://box/etc/hosts"),
                remote("SSH://me@box.lan/a/./b//c/../d"),
                remote("ssh://box"),
                remote("ssh://box/"),
                remote("ssh://box/~"),
                remote("ssh://box/~/notes/a.md"),
                remote("ssh://box/~notes/a.md"),
                remote("ssh://box/a/~/b"),
                remote("ssh://box/~/-rf"),
                remote("ssh://box/x'; rm -rf ~ #"),
            ],
            [
                at("box", "/etc/hosts"),
                at("me@box.lan", "/a/b/d"),
                at("box", "/"),
                at("box", "/"),
                at("box", "."),
                at("box", "notes/a.md"),
                at("box", "/~notes/a.md"),
                at("box", "/a/~/b"),
                at("box", "-rf"),
                at("box", "/x'; rm -rf ~ #"),
            ]
            .map(Ok)
        );
    }

    #[test]
    fn an_ssh_url_rejects_an_option_or_shell_text_as_host_and_a_path_above_its_root() {
        let host = |host: &str| {
            Err(UrlError::Host {
                host: host.to_owned(),
            })
        };
        let escapes = |path: &str| {
            Err(UrlError::Escapes {
                scheme: "ssh",
                path: path.to_owned(),
            })
        };
        assert_eq!(
            [
                remote("ssh:///etc/hosts"),
                remote("ssh://-oProxyCommand=touch%20x/etc"),
                remote("ssh://box;id/etc"),
                remote("ssh://$(id)/etc"),
                remote("ssh://box id/etc"),
                remote("ssh://`id`/etc"),
                remote("ssh://box:22/etc"),
                remote("ssh://box/../etc"),
                remote("ssh://box/~/../etc"),
                remote("ssh://box/~/a/../../b"),
            ],
            [
                host(""),
                host("-oProxyCommand=touch%20x"),
                host("box;id"),
                host("$(id)"),
                host("box id"),
                host("`id`"),
                host("box:22"),
                escapes("box/../etc"),
                escapes("box/~/../etc"),
                escapes("box/~/a/../../b"),
            ]
        );
    }
}
