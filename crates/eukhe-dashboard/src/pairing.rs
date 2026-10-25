//! Pairing: the token a tab must present before the bridge runs anything
//! for it. The token is 32 random bytes, kept as 64 hex digits in a file
//! of the agent dir (mode 0600), so a link that holds it keeps working
//! across restarts until a rotation replaces it. `eukhe dashboard` puts
//! the token in the URL's fragment, which the browser never sends to a
//! server; the app sends it in the first frame of each socket.
//!
//! Every frame reads the file again, so a rotation by another
//! `eukhe dashboard` process takes effect at the next frame of every socket
//! of this one. The comparison of two tokens is constant-time and stays
//! here (a primitive, like a hash). The token never goes into a log line or
//! an error text.
//!
//! Every choice runs as the compiled Bend core (`bend/ffi_dash.bend`): what
//! a presented text and the file hold and what a start does with the file
//! (its call, `bend/dash.bend` section 1), and what each frame of a socket
//! means (one [`Gate`] per socket, its stepper, section 2). This module
//! reads frames and the file, compares tokens and does what the core
//! answers.

use std::fmt;
use std::io::Write;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::Path;

use anyhow::Context;
use eukhe_bend::wire::{Reader, WireError, Writer, STR_MAX};
use eukhe_bend::{call, expect_core, Entry, Error, Stepper};
use subtle::ConstantTimeEq;

/// The bytes of a token.
const TOKEN_BYTES: usize = 32;

/// A pairing token. Its `Debug` hides the value; only
/// [`PairingToken::secret_hex`] shows it.
#[derive(Clone, PartialEq, Eq)]
pub struct PairingToken([u8; TOKEN_BYTES]);

impl fmt::Debug for PairingToken {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("PairingToken(..)")
    }
}

impl PairingToken {
    /// A new random token.
    fn fresh() -> anyhow::Result<Self> {
        let mut bytes = [0; TOKEN_BYTES];
        getrandom::fill(&mut bytes)
            .map_err(|error| anyhow::anyhow!("get random bytes for the pairing token: {error}"))?;
        Ok(Self(bytes))
    }

    /// The token as 64 lowercase hex digits: the text of the file and of
    /// the URL fragment. Never log it.
    #[must_use]
    pub fn secret_hex(&self) -> String {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";
        let mut hex = String::with_capacity(TOKEN_BYTES * 2);
        for byte in self.0 {
            hex.push(char::from(DIGITS[usize::from(byte >> 4)]));
            hex.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
        }
        hex
    }

    /// Whether `other` is this token, in constant time.
    fn same(&self, other: &Self) -> bool {
        bool::from(self.0.ct_eq(&other.0))
    }
}

/// Whether `eukhe dashboard` keeps the stored token or replaces it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rotation {
    /// Use the stored token; make one when there is none.
    Keep,
    /// Replace the stored token with a new one: every earlier token stops
    /// working.
    Rotate,
}

/// The pairing token stored at `path`: the stored one, or a new one when
/// there is none or `rotation` asks for one. A new token replaces the
/// file atomically (mode 0600); a kept file with a wider mode is set to
/// 0600.
///
/// # Errors
///
/// The file cannot be read or written, or it holds no token (rotate to
/// replace it).
pub fn pairing_token(path: &Path, rotation: Rotation) -> anyhow::Result<PairingToken> {
    let disk = Disk::of(path, std::fs::read_to_string(path));
    let mode = match &disk {
        Disk::Text(_) => std::fs::metadata(path)
            .with_context(|| format!("read the mode of {}", path.display()))?
            .permissions()
            .mode(),
        Disk::Missing | Disk::Unreadable(_) => 0,
    };
    let mut writer = Writer::new();
    writer.tag(2).tag(match rotation {
        Rotation::Keep => 0,
        Rotation::Rotate => 1,
    });
    disk.spell(&mut writer);
    writer.nat(u64::from(mode));
    let keep = ask(&mut writer, |reader| reader.tag_of(5, "a start choice"));
    match (keep, disk) {
        (0, _) => store_fresh(path),
        (1 | 2, disk) => {
            let token = stored(&disk).unwrap_or_else(|| inconsistent("a stored token"));
            if keep == 2 {
                std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600))
                    .with_context(|| format!("make {} private", path.display()))?;
            }
            Ok(token)
        }
        (3, Disk::Unreadable(error)) => {
            Err(error).with_context(|| format!("read {}", path.display()))
        }
        (3, Disk::Missing | Disk::Text(_)) => inconsistent("an unreadable file"),
        (4.., _) => Err(anyhow::anyhow!(
            "{} holds no pairing token: run `eukhe dashboard --rotate-token` to make a new one",
            path.display()
        )),
    }
}

/// Make a new token and store it at `path`.
fn store_fresh(path: &Path) -> anyhow::Result<PairingToken> {
    let token = PairingToken::fresh()?;
    write_private(path, format!("{}\n", token.secret_hex()).as_bytes())?;
    Ok(token)
}

/// Write `contents` to `path` with mode 0600: a new file in the same
/// folder, synced, then renamed over `path`, so a reader sees the old
/// file or the new one, never a part.
///
/// # Errors
///
/// The folder cannot be made, or the file cannot be written or renamed.
pub(crate) fn write_private(path: &Path, contents: &[u8]) -> anyhow::Result<()> {
    let folder = path
        .parent()
        .with_context(|| format!("{} has no folder", path.display()))?;
    std::fs::create_dir_all(folder).with_context(|| format!("create {}", folder.display()))?;
    let name = path
        .file_name()
        .with_context(|| format!("{} has no file name", path.display()))?
        .to_string_lossy();
    let staging = folder.join(format!(".{name}.{}.tmp", uuid::Uuid::new_v4()));
    let written = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&staging)
        .and_then(|mut file| {
            file.write_all(contents)?;
            file.sync_all()
        })
        .and_then(|()| std::fs::rename(&staging, path));
    if let Err(error) = written {
        if let Err(cleanup) = std::fs::remove_file(&staging) {
            if cleanup.kind() != std::io::ErrorKind::NotFound {
                tracing::warn!(path = %staging.display(), error = %cleanup, "could not remove a staging file");
            }
        }
        return Err(error).with_context(|| format!("write {}", path.display()));
    }
    Ok(())
}

/// Write the page that opens `url` (which holds the token) in the
/// browser to `path`, mode 0600: the browser gets the page's path, so the
/// token never goes into a process's arguments, which other users of the
/// machine can read.
///
/// # Errors
///
/// The page cannot be written.
pub fn opener_page(path: &Path, url: &str) -> anyhow::Result<()> {
    let url = url
        .replace('&', "&amp;")
        .replace('"', "&quot;")
        .replace('<', "&lt;");
    let page = format!(
        "<!doctype html>\n<meta charset=\"utf-8\">\n<meta name=\"referrer\" content=\"no-referrer\">\n<meta http-equiv=\"refresh\" content=\"0;url={url}\">\n<title>eukhe dashboard</title>\n<a href=\"{url}\">Open the eukhe dashboard</a>\n"
    );
    write_private(path, page.as_bytes())
}

/// What reading the token file met (`Disk` in `bend/dash.bend`).
pub(crate) enum Disk {
    /// The file does not exist.
    Missing,
    /// It could not be read (or is not UTF-8).
    Unreadable(std::io::Error),
    /// Its text.
    Text(String),
}

impl Disk {
    /// What a read of the file at `path` met.
    fn of(path: &Path, read: std::io::Result<String>) -> Disk {
        match read {
            Ok(text) => Disk::Text(text),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Disk::Missing,
            Err(error) => {
                tracing::warn!(path = %path.display(), %error, "could not read the pairing token");
                Disk::Unreadable(error)
            }
        }
    }

    /// The token file at `path`, read now.
    pub(crate) async fn read(path: &Path) -> Disk {
        Disk::of(path, tokio::fs::read_to_string(path).await)
    }

    /// The file on the wire: a text longer than the wire carries is `huge`.
    fn spell(&self, writer: &mut Writer) {
        match self {
            Disk::Missing => writer.tag(0),
            Disk::Unreadable(_) => writer.tag(1),
            Disk::Text(text) if text.chars().count() <= STR_MAX => writer.tag(2).str(text),
            Disk::Text(_) => writer.tag(3),
        };
    }
}

/// A presented text on the wire (`Said`): one longer than the wire
/// carries is `overlong`.
fn said(writer: &mut Writer, text: &str) {
    if text.chars().count() <= STR_MAX {
        writer.tag(0).str(text);
    } else {
        writer.tag(1);
    }
}

/// The first frame of a socket (`First` in `bend/dash.bend`).
pub(crate) enum First {
    /// A binary frame, none in time, or the tab left.
    NoText,
    /// A text frame that is not a pairing.
    NotPairing,
    /// A pairing that presents this text.
    Pair(String),
}

/// A reply of the compiled core that its laws rule out: only an
/// inconsistent build answers it.
fn inconsistent<T>(expected: &'static str) -> T {
    expect_core(
        Entry::Dash,
        Err::<T, Error>(Error::Wire(WireError::Malformed { at: 0, expected })),
    )
}

/// The compiled core's answer to the request in `writer`, read by `read`.
fn ask<T>(writer: &mut Writer, read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>) -> T {
    let answer = || -> Result<T, Error> {
        let reply = call(Entry::Dash, &writer.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let value = read(&mut reader)?;
        reader.end()?;
        Ok(value)
    };
    expect_core(Entry::Dash, answer())
}

/// A token in a reply: tag 0 and its bytes, or another of `tags` tags.
fn read_token(reader: &mut Reader<'_>, tags: u32) -> Result<Option<PairingToken>, WireError> {
    let bad = WireError::Malformed {
        at: 0,
        expected: "the 32 bytes of a token",
    };
    match reader.tag_of(tags, "a token")? {
        0 => {
            if reader.count()? != TOKEN_BYTES {
                return Err(bad);
            }
            let mut bytes = [0; TOKEN_BYTES];
            for byte in &mut bytes {
                *byte = u8::try_from(reader.nat()?).map_err(|_| bad.clone())?;
            }
            Ok(Some(PairingToken(bytes)))
        }
        1.. => Ok(None),
    }
}

/// The token a presented text spells, if any.
fn presented(text: &str) -> Option<PairingToken> {
    let mut writer = Writer::new();
    writer.tag(0);
    said(&mut writer, text);
    ask(&mut writer, |reader| read_token(reader, 3))
}

/// The token the file holds, if any.
fn stored(disk: &Disk) -> Option<PairingToken> {
    let mut writer = Writer::new();
    writer.tag(1);
    disk.spell(&mut writer);
    ask(&mut writer, |reader| read_token(reader, 2))
}

/// Both tokens exist and are equal (in constant time).
fn equal(presented: Option<&PairingToken>, stored: Option<&PairingToken>) -> bool {
    presented
        .zip(stored)
        .is_some_and(|(presented, stored)| presented.same(stored))
}

/// What the host does with a frame of a socket (`Verdict` in
/// `bend/dash.bend`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Verdict {
    /// The socket opens: greet the tab.
    Paired,
    /// The frame runs.
    Run,
    /// Tell the tab this text (an `unpaired` frame) and close the socket.
    Refuse(String),
    /// The socket is closed: nothing runs.
    Closed,
}

/// One socket's pairing gate: its stepper in the compiled core
/// (`bend/dash.bend` section 2), which decides what each frame means, and
/// the token the socket's first frame presented, which only the
/// constant-time comparison reads.
#[derive(Debug)]
pub(crate) struct Gate {
    stepper: Stepper,
    presented: Option<PairingToken>,
}

impl Gate {
    /// The gate of a new socket: it waits for its pairing.
    pub(crate) fn open() -> Gate {
        let (stepper, reply) = expect_core(Entry::Dash, Stepper::open(Entry::Dash, ""));
        expect_core(Entry::Dash, Reader::reply(&reply).and_then(Reader::end));
        Gate {
            stepper,
            presented: None,
        }
    }

    /// The socket's first frame, with the token file as `disk`.
    pub(crate) fn first(&mut self, first: &First, disk: &Disk) -> Verdict {
        self.presented = match first {
            First::Pair(text) => presented(text),
            First::NoText | First::NotPairing => None,
        };
        let mut event = Writer::new();
        event.tag(0);
        match first {
            First::NoText => event.tag(0),
            First::NotPairing => event.tag(1),
            First::Pair(text) => {
                event.tag(2);
                said(&mut event, text);
                &mut event
            }
        };
        disk.spell(&mut event);
        event.bool(equal(self.presented.as_ref(), stored(disk).as_ref()));
        self.step(&mut event)
    }

    /// A later text frame of the socket, with the token file as `disk`.
    pub(crate) fn frame(&mut self, disk: &Disk) -> Verdict {
        let mut event = Writer::new();
        event.tag(1);
        disk.spell(&mut event);
        event.bool(equal(self.presented.as_ref(), stored(disk).as_ref()));
        self.step(&mut event)
    }

    /// The stepper's verdict on the event in `event`.
    fn step(&mut self, event: &mut Writer) -> Verdict {
        let mut answer = || -> Result<Verdict, Error> {
            let reply = self.stepper.step(&event.finish()?)?;
            let mut reader = Reader::reply(&reply)?;
            let verdict = match reader.tag_of(4, "a verdict")? {
                0 => Verdict::Paired,
                1 => Verdict::Run,
                2 => Verdict::Refuse(reader.str()?.to_owned()),
                3.. => Verdict::Closed,
            };
            reader.end()?;
            Ok(verdict)
        };
        expect_core(Entry::Dash, answer())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_opener_page_is_private_and_redirects() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("dashboard-open.html");
        opener_page(&path, "http://127.0.0.1:8377/#token=ab").expect("written");
        assert_eq!(
            (
                std::fs::metadata(&path).expect("metadata").permissions().mode() & 0o777,
                std::fs::read_to_string(&path).expect("read"),
            ),
            (
                0o600,
                "<!doctype html>\n<meta charset=\"utf-8\">\n<meta name=\"referrer\" content=\"no-referrer\">\n<meta http-equiv=\"refresh\" content=\"0;url=http://127.0.0.1:8377/#token=ab\">\n<title>eukhe dashboard</title>\n<a href=\"http://127.0.0.1:8377/#token=ab\">Open the eukhe dashboard</a>\n".to_string()
            )
        );
    }

    #[test]
    fn a_token_is_kept_private_until_rotated() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("agent").join("dashboard-token");
        let first = pairing_token(&path, Rotation::Keep).expect("made");
        let mode = |path: &Path| {
            std::fs::metadata(path)
                .expect("metadata")
                .permissions()
                .mode()
                & 0o777
        };
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).expect("chmod");
        let kept = pairing_token(&path, Rotation::Keep).expect("kept");
        let kept_mode = mode(&path);
        let rotated = pairing_token(&path, Rotation::Rotate).expect("rotated");
        let stored = std::fs::read_to_string(&path).expect("stored");
        let leftovers: Vec<_> = std::fs::read_dir(path.parent().expect("folder"))
            .expect("list")
            .map(|entry| entry.expect("entry").file_name())
            .collect();
        assert_eq!(
            (
                kept == first,
                kept_mode,
                rotated == first,
                mode(&path),
                stored,
                leftovers,
                format!("{rotated:?}"),
            ),
            (
                true,
                0o600,
                false,
                0o600,
                format!("{}\n", rotated.secret_hex()),
                vec![std::ffi::OsString::from("dashboard-token")],
                "PairingToken(..)".to_string(),
            )
        );
    }

    #[test]
    fn a_damaged_file_is_an_error_without_its_text() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("dashboard-token");
        std::fs::write(&path, "secret-but-not-a-token\n").expect("write");
        let error = format!(
            "{:#}",
            pairing_token(&path, Rotation::Keep).expect_err("damaged")
        );
        assert_eq!(
            error,
            format!(
                "{} holds no pairing token: run `eukhe dashboard --rotate-token` to make a new one",
                path.display()
            )
        );
    }

    /// Each socket's gate pairs only on the file's token and ends at the
    /// first frame after a rotation; nothing runs after a refusal (laws
    /// `dash_conn_*` pin every verdict).
    #[tokio::test]
    async fn a_socket_runs_only_while_its_token_is_the_files() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("dashboard-token");
        let mut unset = Gate::open();
        let none = unset.first(
            &First::Pair(PairingToken([1; TOKEN_BYTES]).secret_hex()),
            &Disk::read(&path).await,
        );
        let first = pairing_token(&path, Rotation::Keep).expect("made");
        let mut tab = Gate::open();
        let mut run = vec![tab.first(&First::Pair(first.secret_hex()), &Disk::read(&path).await)];
        run.push(tab.frame(&Disk::read(&path).await));
        let second = pairing_token(&path, Rotation::Rotate).expect("rotated");
        run.push(tab.frame(&Disk::read(&path).await));
        run.push(tab.frame(&Disk::read(&path).await));
        let mut old = Gate::open();
        let mut junk = Gate::open();
        let mut fresh = Gate::open();
        let wrong =
            "this pairing link is not valid any more: open the link that `eukhe dashboard` prints";
        assert_eq!(
            (
                none,
                run,
                old.first(&First::Pair(first.secret_hex()), &Disk::read(&path).await),
                junk.first(&First::Pair("x".to_owned()), &Disk::read(&path).await),
                junk.frame(&Disk::read(&path).await),
                fresh.first(
                    &First::Pair(second.secret_hex().to_uppercase()),
                    &Disk::read(&path).await
                ),
                fresh.frame(&Disk::read(&path).await),
            ),
            (
                Verdict::Refuse(
                    "the dashboard has no pairing token: restart `eukhe dashboard`".to_owned()
                ),
                vec![
                    Verdict::Paired,
                    Verdict::Run,
                    Verdict::Refuse(wrong.to_owned()),
                    Verdict::Closed
                ],
                Verdict::Refuse(wrong.to_owned()),
                Verdict::Refuse(wrong.to_owned()),
                Verdict::Closed,
                Verdict::Paired,
                Verdict::Run,
            )
        );
    }
}
