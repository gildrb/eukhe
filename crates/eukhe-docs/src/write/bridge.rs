//! The bridge from the locked writes (an edit of many files, the write
//! tool, `MV`, the sweep of temporary files) to their Bend model
//! (`bend/doc_commit.bend`, laws in `laws/doc_commit.bend`): generated
//! scenarios run through the real code, and `bridge/bridge_doc_commit.bend`
//! must print the same transcript, byte for byte. That file gives the
//! events and the transcript lines.

use std::ffi::OsString;
use std::fmt::Write as _;
use std::fs::File;
use std::path::{Path, PathBuf};

use super::{temp_prefix, Faults, LockedWriter, Stage, WriteError};
use crate::error::EditError;
use crate::hashline::{
    apply_hashline, EditWriter, FileChange, HashlineOptions, Published, WriteRequest,
};
use crate::store::EditStore;
use crate::testing::{compare, Rng, Scenario};
use crate::{Documents, ReadContent};

const MODEL: &str = "bridge/bridge_doc_commit.bend";

/// The ` I` of each index, as the model prints a list.
fn indices(list: &[impl std::fmt::Display]) -> String {
    let mut text = String::new();
    for at in list {
        write!(text, " {at}").unwrap();
    }
    text
}

/// A scratch directory: the files under `files/`, the path locks under
/// `locks/`.
struct Scratch {
    _dir: tempfile::TempDir,
    root: PathBuf,
    locks: PathBuf,
}

impl Scratch {
    fn new() -> Self {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join("files");
        std::fs::create_dir(&root).unwrap();
        Self {
            locks: dir.path().join("locks"),
            root,
            _dir: dir,
        }
    }
}

// Edit
// ----

/// One file of a generated edit: `MOVE` moves it to a free name, else it
/// gets a line at its end; `changed`: another program rewrites it after
/// the edit staged it; `fault`: the model's fault number (0 none, 1 the
/// directory sync fails, 2 the publish fails, 3 the source removal fails).
struct Planned {
    moves: bool,
    changed: bool,
    fault: u64,
}

/// Fails each `(file name, stage)` it holds.
struct Injected(Vec<(OsString, Stage)>);

impl Faults for Injected {
    fn inject(&self, target: &Path, stage: Stage) -> std::io::Result<()> {
        let hit = self
            .0
            .iter()
            .any(|(name, at)| *at == stage && target.file_name() == Some(name.as_os_str()));
        if hit {
            return Err(std::io::Error::other("injected"));
        }
        Ok(())
    }
}

/// A writer that lets another program rewrite files after the edit was
/// staged, then calls the real writer.
struct Interloper<'a> {
    inner: LockedWriter<'a>,
    changed: Vec<PathBuf>,
}

impl EditWriter for Interloper<'_> {
    fn write_all(&self, requests: &[WriteRequest<'_>]) -> Result<Vec<Published>, EditError> {
        for path in &self.changed {
            std::fs::write(path, "changed by another program\n").unwrap();
        }
        self.inner.write_all(requests)
    }
}

/// What the real code does with the edit of `files`, as the model prints
/// it.
fn edited(files: &[Planned]) -> String {
    let scratch = Scratch::new();
    let store = EditStore::new();
    let mut sections = Vec::new();
    let mut faults = Vec::new();
    let mut changed = Vec::new();
    for (at, file) in files.iter().enumerate() {
        let name = format!("f{at}.txt");
        let path = scratch.root.join(&name);
        std::fs::write(&path, "x\n").unwrap();
        let tag = store.record(
            &eukhe_types::path_policy::real_path(&path),
            "x\n",
            Some(&[1]),
        );
        let destination = format!("g{at}.txt");
        let target = if file.moves {
            sections.push(format!("[{name}#{tag}]\nMV {destination}"));
            destination
        } else {
            sections.push(format!("[{name}#{tag}]\nPUT >1:\n+e{at}"));
            name.clone()
        };
        match file.fault {
            0 => {}
            1 => faults.push((OsString::from(target), Stage::AfterRename)),
            2 => faults.push((OsString::from(target), Stage::BeforeRename)),
            3.. => faults.push((OsString::from(name), Stage::RemoveSource)),
        }
        if file.changed {
            changed.push(path);
        }
    }
    let faults = Injected(faults);
    let writer = Interloper {
        inner: LockedWriter {
            lock_dir: &scratch.locks,
            gate: &crate::gate::Open,
            faults: &faults,
        },
        changed,
    };
    let reply = apply_hashline(
        &sections.join("\n"),
        &HashlineOptions {
            cwd: &scratch.root,
            home: None,
            enforce_seen_lines: true,
        },
        &store,
        &writer,
    );
    let landed: Vec<usize> = (0..files.len())
        .filter(|&at| {
            if files[at].moves {
                scratch.root.join(format!("g{at}.txt")).exists()
            } else {
                std::fs::read_to_string(scratch.root.join(format!("f{at}.txt"))).unwrap()
                    == format!("x\ne{at}\n")
            }
        })
        .collect();
    let (result, applied, warned) = match reply {
        Err(_) => ("rejected", Vec::new(), Vec::new()),
        Ok(outcome) => {
            let applied: Vec<usize> = (0..outcome.files.len())
                .filter(|&at| match outcome.files[at].change {
                    FileChange::Updated | FileChange::Moved { .. } | FileChange::Deleted => true,
                    FileChange::Unchanged | FileChange::NotWritten { .. } => false,
                })
                .collect();
            let warned = applied
                .iter()
                .copied()
                .filter(|&at| !outcome.files[at].warnings.is_empty())
                .collect();
            let result = if applied.len() == outcome.files.len() {
                "applied"
            } else {
                "partial"
            };
            (result, applied, warned)
        }
    };
    format!(
        "r {result}\nl{}\np{}\nw{}\n",
        indices(&landed),
        indices(&applied),
        indices(&warned)
    )
}

/// An edit reports applied exactly the files that landed, and lands no
/// file when one changed, on 300 scenarios of 1 to 5 files: updates and
/// moves, conflicts, failed publishes, failed directory syncs and failed
/// source removals at any file.
#[test]
fn an_edit_of_many_files_runs_as_its_model() {
    let mut rng = Rng(0x0ed1_7c0d_e5ee_d001);
    let scenarios = (0..300).map(|at| {
        let files: Vec<Planned> = (0..rng.range(1, 5))
            .map(|_| Planned {
                moves: rng.below(3) == 0,
                changed: rng.below(10) == 0,
                fault: match rng.below(8) {
                    0..=3 => 0,
                    4 => 1,
                    5 => 2,
                    6.. => 3,
                },
            })
            .collect();
        let events: Vec<String> = files
            .iter()
            .map(|file| {
                format!(
                    "e {} {} {}",
                    u8::from(file.moves),
                    u8::from(file.changed),
                    file.fault
                )
            })
            .collect();
        Scenario {
            name: format!("edit-{at}"),
            events: events.join("\n"),
            transcript: edited(&files),
        }
    });
    compare(MODEL, scenarios.collect::<Vec<_>>());
}

// Write
// -----

/// The write tool replaces a file only when the session saw its bytes, on
/// 200 scenarios of session reads and writes and another program's writes
/// and deletes of one file.
#[test]
fn the_write_tool_runs_as_its_model() {
    let mut rng = Rng(0x0ed1_7c0d_e5ee_d002);
    let scenarios = (0..200).map(|at| {
        let scratch = Scratch::new();
        let documents = Documents::new(scratch.locks.clone(), None);
        let path = scratch.root.join("w.txt");
        let mut events = Vec::new();
        let mut transcript = String::new();
        for _ in 0..rng.range(1, 20) {
            match rng.below(8) {
                0 | 1 => {
                    let read = documents.read(&scratch.root, "w.txt", &crate::gate::Open);
                    assert_eq!(read.is_ok(), path.exists(), "{read:?}");
                    events.push("r".to_owned());
                }
                2 | 3 => {
                    let content = rng.below(12);
                    std::fs::write(&path, format!("v{content}\n")).unwrap();
                    events.push(format!("x {content}"));
                }
                4 => {
                    if path.exists() {
                        std::fs::remove_file(&path).unwrap();
                    }
                    events.push("d".to_owned());
                }
                5.. => {
                    let content = rng.below(12);
                    let written = documents.write(
                        &scratch.root,
                        "w.txt",
                        &format!("v{content}\n"),
                        &crate::gate::Open,
                    );
                    let line = match written {
                        Ok(_) => "w ok\n",
                        Err(WriteError::Unseen { .. }) => "w refused\n",
                        Err(error) => panic!("{error}"),
                    };
                    transcript.push_str(line);
                    events.push(format!("w {content}"));
                }
            }
        }
        Scenario {
            name: format!("write-{at}"),
            events: events.join("\n"),
            transcript,
        }
    });
    compare(MODEL, scenarios.collect::<Vec<_>>());
}

// Move
// ----

/// The files `n0`..`n5` under `root`, as the model prints them.
fn file_set(root: &Path) -> String {
    let mut line = "s".to_owned();
    for name in 0..6 {
        if let Ok(text) = std::fs::read_to_string(root.join(format!("n{name}"))) {
            let content = text.trim_start_matches('c').trim_end_matches('\n');
            write!(line, " {name}:{content}").unwrap();
        }
    }
    line.push('\n');
    line
}

/// `MV` never replaces a file and moves a file to a free name, on 200
/// scenarios of a random file set over 6 names and 1 to 6 moves.
#[test]
fn a_move_runs_as_its_model() {
    let mut rng = Rng(0x0ed1_7c0d_e5ee_d003);
    let scenarios = (0..200).map(|at| {
        let scratch = Scratch::new();
        let documents = Documents::new(scratch.locks.clone(), None);
        let mut events = Vec::new();
        let mut transcript = String::new();
        for name in 0..6 {
            if rng.below(2) == 0 {
                let content = rng.below(10);
                std::fs::write(
                    scratch.root.join(format!("n{name}")),
                    format!("c{content}\n"),
                )
                .unwrap();
                events.push(format!("f {name} {content}"));
            }
        }
        for _ in 0..rng.range(1, 6) {
            let present: Vec<u64> = (0..6)
                .filter(|name| scratch.root.join(format!("n{name}")).exists())
                .collect();
            if present.is_empty() {
                break;
            }
            let source =
                present[usize::try_from(rng.below(u64::try_from(present.len()).unwrap())).unwrap()];
            let target = (source + rng.range(1, 5)) % 6;
            let view = documents
                .read(&scratch.root, &format!("n{source}"), &crate::gate::Open)
                .unwrap();
            let tag = match view.content {
                ReadContent::File(file) => file.tag.unwrap(),
                ReadContent::Directory(entries) => panic!("n{source} is a directory: {entries:?}"),
            };
            let moved = documents.edit(
                &scratch.root,
                &format!("[n{source}#{tag}]\nMV n{target}"),
                &crate::gate::Open,
            );
            let line = match moved {
                Ok(_) => "m ok\n".to_owned(),
                Err(error) if error.to_string().contains("MV destination") => {
                    "m exists\n".to_owned()
                }
                Err(error) => panic!("{error}"),
            };
            transcript.push_str(&line);
            transcript.push_str(&file_set(&scratch.root));
            events.push(format!("m {source} {target}"));
        }
        Scenario {
            name: format!("move-{at}"),
            events: events.join("\n"),
            transcript,
        }
    });
    compare(MODEL, scenarios.collect::<Vec<_>>());
}

// Sweep
// -----

/// A write of a file removes the temporary files of that file that no
/// live writer holds, and keeps every other entry, on 200 scenarios of 1
/// to 8 entries: temporary files of the target and of another file, and
/// other files, each held by a live writer or not.
#[test]
fn the_temp_sweep_runs_as_its_model() {
    let mut rng = Rng(0x0ed1_7c0d_e5ee_d004);
    let scenarios = (0..200).map(|at| {
        let scratch = Scratch::new();
        let documents = Documents::new(scratch.locks.clone(), None);
        let target = scratch.root.join("t.txt");
        std::fs::write(&target, "old\n").unwrap();
        let own = temp_prefix(&target);
        let foreign = temp_prefix(&scratch.root.join("u.txt"));
        let mut events = Vec::new();
        let mut entries = Vec::new();
        let mut held = Vec::new();
        for id in 1..=rng.range(1, 8) {
            let sort = rng.below(3);
            let holds = rng.below(2) == 0;
            let path = scratch.root.join(match sort {
                0 => format!("{own}{id}-0"),
                1 => format!("{foreign}{id}-0"),
                2.. => format!("o{id}"),
            });
            std::fs::write(&path, "partial").unwrap();
            if holds {
                let file = File::open(&path).unwrap();
                file.lock().unwrap();
                held.push(file);
            }
            events.push(format!("t {id} {sort} {}", u8::from(holds)));
            entries.push((id, path));
        }
        documents
            .read(&scratch.root, "t.txt", &crate::gate::Open)
            .unwrap();
        documents
            .write(&scratch.root, "t.txt", "new\n", &crate::gate::Open)
            .unwrap();
        let removed: Vec<u64> = entries
            .iter()
            .filter(|(_, path)| !path.exists())
            .map(|(id, _)| *id)
            .collect();
        drop(held);
        Scenario {
            name: format!("sweep-{at}"),
            events: events.join("\n"),
            transcript: format!("x{}\n", indices(&removed)),
        }
    });
    compare(MODEL, scenarios.collect::<Vec<_>>());
}
