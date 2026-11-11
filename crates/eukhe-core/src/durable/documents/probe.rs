//! The documents tools' writes as an exactly-once effect (spec O1-O8,
//! `eukhe_bend::rules::once`). Before any file of a call can change, the
//! call records in its tool task ([`ToolExecutionApi::probe`], durable
//! before it returns) every file it is about to change, with the sha-256
//! of the bytes it replaces and of the bytes it writes ([`ProbeWitness`]).
//! A restart that finds the call started and unsettled looks at those
//! files ([`probe`]): each holds its new bytes, the write landed; each
//! holds its old bytes, it never will (the process that wrote is dead);
//! anything else, nobody can tell.

use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_bend::rules::once::Seen;
use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_docs::{Change, Witness};
use eukhe_durable::harness::types::{ToolExecutionApi, ToolProbe};
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// A file a call is about to change: its real path and the digests of the
/// bytes it replaces and of the bytes it writes (`None`: no file).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct ProbedFile {
    path: PathBuf,
    base: Option<String>,
    next: Option<String>,
}

/// The record of a call: every file it is about to change.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
struct WriteProbe {
    files: Vec<ProbedFile>,
}

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// The [`Witness`] of one documents tool call: it keeps every change the
/// call's writes told it, one per file (a rebase replaces its file's), and
/// records them all in the call's task before the write goes on.
pub(super) struct ProbeWitness {
    api: Arc<dyn ToolExecutionApi>,
    cx: Context,
    /// The runtime the record commits on; the witness runs on a blocking
    /// thread of it.
    runtime: tokio::runtime::Handle,
    probe: Mutex<WriteProbe>,
}

impl ProbeWitness {
    pub(super) fn new(api: Arc<dyn ToolExecutionApi>, cx: &Context) -> Self {
        Self {
            api,
            cx: cx.clone(),
            runtime: tokio::runtime::Handle::current(),
            probe: Mutex::new(WriteProbe::default()),
        }
    }
}

impl Witness for ProbeWitness {
    fn changing(&self, changes: &[Change<'_>]) -> std::io::Result<()> {
        let record = {
            let mut probe = self.probe.lock().unwrap_or_else(PoisonError::into_inner);
            for change in changes {
                let file = ProbedFile {
                    path: change.real.to_path_buf(),
                    base: change.base.map(digest),
                    next: change.next.map(digest),
                };
                match probe.files.iter_mut().find(|known| known.path == file.path) {
                    Some(known) => *known = file,
                    None => probe.files.push(file),
                }
            }
            to_json(&*probe).map_err(std::io::Error::other)?
        };
        self.runtime
            .block_on(self.api.probe(record, &self.cx))
            .map_err(std::io::Error::other)
    }
}

/// The probe of the documents tools that write: what the files of a
/// call's record show, read on a blocking thread.
pub(super) fn probe() -> ToolProbe {
    Arc::new(|record: JsonValue| {
        async move {
            // A probe that could not finish tells nothing.
            tokio::task::spawn_blocking(move || seen(&record))
                .await
                .unwrap_or(Seen::Dark)
        }
        .boxed()
    })
}

/// What the files of `record` show: every file holds the bytes the call
/// wrote, [`Seen::Landed`]; every file holds the bytes it replaced,
/// [`Seen::Clean`]; else (a file that holds other bytes or cannot be read,
/// a record that is not a probe's) [`Seen::Dark`].
fn seen(record: &JsonValue) -> Seen {
    let Ok(probe) = from_json::<WriteProbe>(record) else {
        return Seen::Dark;
    };
    if probe.files.is_empty() {
        return Seen::Dark;
    }
    let (mut landed, mut clean) = (true, true);
    for file in &probe.files {
        let now = match std::fs::read(&file.path) {
            Ok(bytes) => Some(digest(&bytes)),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(_) => return Seen::Dark,
        };
        landed &= now == file.next;
        clean &= now == file.base;
    }
    match (landed, clean) {
        (true, _) => Seen::Landed,
        (false, true) => Seen::Clean,
        (false, false) => Seen::Dark,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The probe of `files`, each `(name, base, next)` under `dir`.
    fn record(dir: &std::path::Path, files: &[(&str, Option<&str>, Option<&str>)]) -> JsonValue {
        to_json(&WriteProbe {
            files: files
                .iter()
                .map(|(name, base, next)| ProbedFile {
                    path: dir.join(name),
                    base: base.map(|text| digest(text.as_bytes())),
                    next: next.map(|text| digest(text.as_bytes())),
                })
                .collect(),
        })
        .unwrap()
    }

    #[test]
    fn the_files_tell_whether_a_write_landed() {
        let dir = tempfile::tempdir().unwrap();
        let dir = dir.path();
        std::fs::write(dir.join("new.txt"), "new\n").unwrap();
        std::fs::write(dir.join("old.txt"), "old\n").unwrap();
        std::fs::write(dir.join("other.txt"), "other\n").unwrap();
        let cases = [
            record(dir, &[("new.txt", Some("old\n"), Some("new\n"))]),
            record(dir, &[("old.txt", Some("old\n"), Some("new\n"))]),
            record(dir, &[("other.txt", Some("old\n"), Some("new\n"))]),
            // A created file, there and not yet there.
            record(dir, &[("new.txt", None, Some("new\n"))]),
            record(dir, &[("absent.txt", None, Some("new\n"))]),
            // A removed file.
            record(dir, &[("absent.txt", Some("old\n"), None)]),
            // One file landed, the other not yet: a partial write.
            record(
                dir,
                &[
                    ("new.txt", Some("old\n"), Some("new\n")),
                    ("old.txt", Some("old\n"), Some("new\n")),
                ],
            ),
            record(dir, &[]),
            JsonValue::from(serde_json::json!({ "files": "not a list" })),
        ];
        assert_eq!(
            cases.iter().map(seen).collect::<Vec<_>>(),
            [
                Seen::Landed,
                Seen::Clean,
                Seen::Dark,
                Seen::Landed,
                Seen::Clean,
                Seen::Landed,
                Seen::Dark,
                Seen::Dark,
                Seen::Dark,
            ]
        );
    }
}
