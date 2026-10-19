//! The bridge between the staging code ([`publish`],
//! [`sweep_stale_staging_dirs`], [`list_sessions`] with
//! [`import_legacy_session`]) and its Bend model (`bend/staging.bend`,
//! whose laws `PROOF.bend` proves): both run the same scenarios and must
//! print the same transcript, byte for byte (`bend/bridge_staging.bend`
//! documents the events).
//!
//! A publish scenario moves a staged storage to a target that is absent,
//! an empty directory, a directory with entries, or a file. A sweep
//! scenario builds generated nodes on disk: leftovers, lock files with and
//! without their directory, storages, plain directories and files, at
//! random depths under two roots or hidden inside a storage, some held by
//! a live lock, some a day old. A listing scenario builds a sessions
//! directory of storages, broken and empty directories, hidden storages
//! and legacy files (whose header id is not their stem), lists it, imports
//! every listed legacy file, and lists it again.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::HashMap;
use std::fmt::Write as _;
use std::fs::{File, FileTimes};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::*;
use crate::durable::discovery::tests::{cx, fixture};
use crate::durable::{import_legacy_session, list_sessions, SessionLocation};

const ID: &str = "0123456789abcdef0123456789abcdef";

fn age(path: &Path) {
    File::open(path)
        .expect("open")
        .set_times(
            FileTimes::new()
                .set_modified(SystemTime::now() - STALE_AFTER - Duration::from_hours(1)),
        )
        .expect("set times");
}

fn held(path: &Path) -> File {
    let file = File::create(path).expect("lock file");
    file.lock().expect("lock");
    file
}

/// What the target of a publish holds: 0 the staged storage, 1 an empty
/// directory, 2 a directory with entries, 3 a file.
fn target_tag(target: &Path) -> u8 {
    if target.is_file() {
        3
    } else if target.join("main.jsonl").is_file() {
        0
    } else if std::fs::read_dir(target).expect("target").next().is_some() {
        2
    } else {
        1
    }
}

async fn publish_scenario(tag: u8) -> Scenario {
    let dir = tempfile::tempdir().expect("tempdir");
    let target = dir.path().join("s1");
    let (parent, staging) = staging_dir(&target, StagingKind::Import).expect("staging");
    std::fs::create_dir(&staging).expect("staging");
    std::fs::write(staging.join("main.jsonl"), "{}\n").expect("main");
    match tag {
        0 => {}
        1 => std::fs::create_dir(&target).expect("empty target"),
        2 => {
            std::fs::create_dir(&target).expect("target");
            std::fs::write(target.join("keep"), "x").expect("entry");
        }
        _ => std::fs::write(&target, "x").expect("file target"),
    }
    let done = match publish(&staging, &target, &parent).await {
        Ok(()) => "ok",
        Err(PublishError::TargetExists) => "exists",
        Err(PublishError::Step { action, source, .. }) => panic!("{action}: {source}"),
    };
    Scenario {
        name: format!("publish {tag}"),
        events: format!("p {tag}\n"),
        transcript: format!("p {done}\nt {}\n", target_tag(&target)),
    }
}

fn sweep_scenario(at: usize, rng: &mut Rng) -> Scenario {
    let dir = tempfile::tempdir().expect("tempdir");
    let roots = [
        dir.path().join("sessions"),
        dir.path().join("session-artifacts"),
    ];
    for root in &roots {
        std::fs::create_dir(root).expect("root");
    }
    let mut events = String::new();
    let mut ids: HashMap<PathBuf, u64> = HashMap::new();
    let mut locks = Vec::new();
    for id in 1..=rng.range(1, 12) {
        let sort = rng.below(6);
        let (hold, stale, open) = (rng.chance(40), rng.chance(60), rng.chance(75));
        let root = &roots[usize::from(rng.chance(50))];
        let mut parent = root.clone();
        for depth in 0..rng.below(4) {
            parent = parent.join(format!("p{id}d{depth}"));
        }
        if !open {
            parent = parent.join(format!("store{id}"));
            std::fs::create_dir_all(&parent).expect("storage");
            std::fs::write(parent.join("main.jsonl"), "{}\n").expect("main");
        }
        std::fs::create_dir_all(&parent).expect("parent");
        let label = if rng.chance(50) { "fork" } else { "deleted" };
        let node = parent.join(format!(".n{id}.{label}-{ID}"));
        let lock = lock_path(&node);
        let path = match sort {
            0 => {
                std::fs::create_dir(&node).expect("leftover");
                if hold {
                    locks.push(held(&lock));
                } else if rng.chance(50) {
                    std::fs::write(&lock, "").expect("free lock");
                }
                node
            }
            1 => {
                // Its young directory keeps both.
                std::fs::create_dir(&node).expect("dir");
                if hold {
                    locks.push(held(&lock));
                } else {
                    std::fs::write(&lock, "").expect("lock");
                }
                lock
            }
            2 => {
                if hold {
                    locks.push(held(&lock));
                } else {
                    std::fs::write(&lock, "").expect("lock");
                }
                lock
            }
            3 => {
                let storage = parent.join(format!("s{id}"));
                std::fs::create_dir(&storage).expect("storage");
                std::fs::write(storage.join("main.jsonl"), "{}\n").expect("main");
                storage
            }
            4 => {
                let plain = parent.join(format!("q{id}"));
                std::fs::create_dir(&plain).expect("plain");
                plain
            }
            _ => {
                let file = parent.join(format!("f{id}.import-{ID}"));
                std::fs::write(&file, "x").expect("file");
                file
            }
        };
        if stale {
            age(&path);
        }
        let _ = writeln!(
            events,
            "n {id} {sort} {} {} {}",
            u8::from(hold),
            u8::from(stale),
            u8::from(open)
        );
        ids.insert(path, id);
    }
    let root_refs: Vec<&Path> = roots.iter().map(PathBuf::as_path).collect();
    let sweep = sweep_stale_staging_dirs(&root_refs).expect("sweep");
    assert!(sweep.failed.is_empty(), "{:?}", sweep.failed);
    drop(locks);
    let mut removed: Vec<u64> = sweep
        .removed
        .iter()
        .map(|path| {
            *ids.get(path)
                .unwrap_or_else(|| panic!("removed {}", path.display()))
        })
        .collect();
    removed.sort_unstable();
    let mut transcript = "x".to_owned();
    for id in removed {
        let _ = write!(transcript, " {id}");
    }
    transcript.push('\n');
    Scenario {
        name: format!("sweep {at}"),
        events,
        transcript,
    }
}

/// The name a listing row opens as, back as its number.
fn number(location: &SessionLocation) -> u64 {
    let dir = location.storage_dir();
    let name = dir
        .file_name()
        .and_then(|name| name.to_str())
        .expect("name");
    name.trim_start_matches('s')
        .parse()
        .expect("a numbered storage")
}

async fn listed(sessions: &Path) -> Vec<(u64, SessionLocation)> {
    let mut rows: Vec<(u64, SessionLocation)> = list_sessions(sessions, cx())
        .await
        .into_iter()
        .map(|row| (number(&row.location), row.location))
        .collect();
    rows.sort_by_key(|(n, _)| *n);
    rows
}

fn show(head: &str, rows: &[(u64, SessionLocation)]) -> String {
    let mut text = head.to_owned();
    for (n, _) in rows {
        let _ = write!(text, " {n}");
    }
    text.push('\n');
    text
}

async fn listing_scenario(at: usize, rng: &mut Rng) -> Scenario {
    let fixture = fixture();
    let cwd = fixture.project("work");
    let sessions = fixture.sessions.clone();
    let mut events = String::new();
    // A legacy file `h<n>.jsonl` (header id h<n>), moved to `path`.
    let legacy = |n: u64, path: &Path| {
        let file = fixture.legacy(&format!("h{n}"), &cwd);
        std::fs::rename(file, path).expect("move legacy");
    };
    for n in 1..=rng.range(1, 6) {
        if rng.chance(60) {
            let (main, hidden, readable) = (rng.chance(80), rng.chance(20), rng.chance(70));
            let name = if hidden {
                format!(".s{n}")
            } else {
                format!("s{n}")
            };
            let dir = sessions.join(&name);
            match (main, readable) {
                (true, true) => {
                    let file = sessions.join(format!("tmp{n}.jsonl"));
                    legacy(n, &file);
                    import_legacy_session(&file, &dir, cx())
                        .await
                        .expect("storage");
                    std::fs::remove_file(&file).expect("remove");
                }
                (true, false) => {
                    std::fs::create_dir(&dir).expect("dir");
                    std::fs::write(dir.join("main.jsonl"), "not json\n").expect("main");
                }
                (false, _) => std::fs::create_dir(&dir).expect("dir"),
            }
            let shown = if hidden { 1000 + n } else { n };
            let _ = writeln!(
                events,
                "d {shown} {} {} {}",
                u8::from(main),
                u8::from(hidden),
                u8::from(main && readable)
            );
        }
        if rng.chance(60) {
            let header = rng.chance(80);
            let path = sessions.join(format!("s{n}.jsonl"));
            if header {
                legacy(n, &path);
            } else {
                std::fs::write(&path, "not a header\n").expect("broken legacy");
            }
            let _ = writeln!(events, "l {n} {}", u8::from(header));
        }
    }
    let mut transcript = String::new();
    if !events.is_empty() {
        let before = listed(&sessions).await;
        transcript.push_str(&show("s", &before));
        for (_, location) in &before {
            if let SessionLocation::Legacy(file) = location {
                import_legacy_session(file, &location.storage_dir(), cx())
                    .await
                    .expect("import");
            }
        }
        transcript.push_str(&show("i", &listed(&sessions).await));
    }
    Scenario {
        name: format!("listing {at}"),
        events,
        transcript,
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn staging_sweep_and_listing_run_as_their_model() {
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let mut scenarios = Vec::new();
    for tag in 0..4 {
        scenarios.push(publish_scenario(tag).await);
    }
    for at in 0..60 {
        scenarios.push(sweep_scenario(at, &mut rng));
    }
    for at in 0..30 {
        scenarios.push(listing_scenario(at, &mut rng).await);
    }
    compare("bend/bridge_staging.bend", scenarios);
}
