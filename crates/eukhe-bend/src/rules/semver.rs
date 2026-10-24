//! The release-version rule (`bend/semver.bend`, entry `bend/ffi_semver.bend`;
//! `laws/semver.bend`): the release of a commit from its workspace version
//! and the repository's tags, and whether a release version names a version
//! of the workspace's series. Each function encodes its texts, calls
//! [`Entry::Semver`] and decodes the reply.
//!
//! The model reads numbers in unary, so the entry refuses (a
//! [`crate::WireError::Rejected`] reply) a request whose read texts hold
//! more than 6 digits in a row: no eukhe version comes near it.

use crate::wire::{Reader, Writer};
use crate::{call, Entry, Error};

/// The release of a commit, or why it has none.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Release {
    /// The workspace version is no version `major.minor.patch`.
    NoVersion,
    /// The workspace version is `X.Y.Z` with `Z` above 0: no series start.
    NoSeriesStart,
    /// The next release of the series, `next`, is not newer than the version
    /// tags `newer` (in the order given): a tag of a newer series.
    Behind { next: String, newer: Vec<String> },
    /// The release: its version, its tag and its title.
    Ready {
        version: String,
        tag: String,
        title: String,
    },
}

/// The release of a commit whose workspace version is `workspace`, with the
/// repository's tags `tags` (`Sv.Rel.release`).
///
/// # Errors
///
/// [`Error::Wire`] with [`crate::WireError::Rejected`] when a read text
/// holds more than 6 digits in a row (or a text is past the wire's
/// bounds); else only from an inconsistent build (see
/// [`crate::expect_core`]).
pub fn release(workspace: &str, tags: &[&str]) -> Result<Release, Error> {
    let mut request = Writer::new();
    request.tag(0).str(workspace).count(tags.len());
    for tag in tags {
        request.str(tag);
    }
    let reply = call(Entry::Semver, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let release = match reply.tag_of(4, "a release reply")? {
        0 => Release::NoVersion,
        1 => Release::NoSeriesStart,
        2 => {
            let next = reply.str()?.to_string();
            let count = reply.count()?;
            let mut newer = Vec::with_capacity(count);
            for _ in 0..count {
                newer.push(reply.str()?.to_string());
            }
            Release::Behind { next, newer }
        }
        _ => Release::Ready {
            version: reply.str()?.to_string(),
            tag: reply.str()?.to_string(),
            title: reply.str()?.to_string(),
        },
    };
    reply.end()?;
    Ok(release)
}

/// How a release version relates to the workspace's series.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Series {
    /// The release version is no version `major.minor.patch`.
    NoVersion,
    /// It is not of the workspace's series (or the workspace version is no
    /// version).
    Other,
    /// It is a version of the workspace's series.
    Of,
}

/// Whether `release` names a version of the series of the workspace version
/// `workspace` (`Sv.Ver.parse`, `Sv.Ver.in_series`).
///
/// # Errors
///
/// As [`release`].
pub fn series(workspace: &str, release: &str) -> Result<Series, Error> {
    let mut request = Writer::new();
    request.tag(1).str(workspace).str(release);
    let reply = call(Entry::Semver, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let series = match reply.tag_of(3, "a series reply")? {
        0 => Series::NoVersion,
        1 => Series::Other,
        _ => Series::Of,
    };
    reply.end()?;
    Ok(series)
}

#[cfg(test)]
mod tests {
    use super::{release, series, Release, Series};

    #[test]
    fn the_codec_carries_each_question_through_the_core() {
        assert_eq!(
            release("0.10.0", &["eukhe-v0.10.3", "v1.2.3"]).unwrap(),
            Release::Ready {
                version: "0.10.4".to_string(),
                tag: "eukhe-v0.10.4".to_string(),
                title: "Eukhe v0.10.4".to_string(),
            }
        );
        assert_eq!(
            release("0.10.0", &["eukhe-v0.11.3", "eukhe-v0.10.3"]).unwrap(),
            Release::Behind {
                next: "0.10.4".to_string(),
                newer: vec!["eukhe-v0.11.3".to_string()],
            }
        );
        assert_eq!(series("0.10.0", "0.10.7").unwrap(), Series::Of);
    }
}
