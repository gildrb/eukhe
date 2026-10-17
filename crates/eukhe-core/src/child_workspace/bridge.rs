//! The bridge between the workspace hand-back ([`super::hand_back_at`])
//! and its Bend model (`bend/sandbox.bend`, `back`; the laws in
//! `PROOF.bend`): both run the same scenarios and must print the same
//! transcript, byte for byte.
//!
//! A scenario is a set of paths and the parent's, the base's and the
//! child's files over them (`bend/bridge_sandbox.bend` documents the
//! format). The driver writes the three workspaces as real directories,
//! runs the hand-back on them, and prints the parent's workspace after it
//! and the conflicts it reported.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::{hand_back_at, write_json, CopyReport, Manifest, BASE, MANIFEST, TREE};

/// The largest path of a scenario.
const PATHS: u64 = 10;
/// The largest content of a scenario.
const VALUES: u64 = 3;

/// A case the scenarios must reach, so that the bridge checks every rule
/// of the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// The child did not change the path.
    Kept,
    /// Only the child changed the path.
    Taken,
    /// Only the child changed the path: it removed it.
    TakenRemoval,
    /// Both changed the path to the same content.
    Same,
    /// Both changed the path differently.
    Conflict,
    /// Both changed the path differently, one of them by removing it.
    RemovalConflict,
}

/// The file name of path `k`: names sort as the numbers do.
fn name(k: u64) -> String {
    format!("f{k:02}")
}

/// A file content, or none.
fn draw(rng: &mut Rng) -> Option<u64> {
    if rng.chance(25) {
        None
    } else {
        Some(rng.range(1, VALUES))
    }
}

/// One scenario: its events and the Rust transcript.
fn scenario(rng: &mut Rng, reached: &mut BTreeSet<Case>) -> (String, String) {
    let keys: BTreeSet<u64> = (0..rng.range(1, 6)).map(|_| rng.below(PATHS)).collect();
    let dir = tempfile::tempdir().unwrap();
    let (parent, root) = (dir.path().join("parent"), dir.path().join("workspace"));
    for side in [parent.clone(), root.join(BASE), root.join(TREE)] {
        fs::create_dir_all(side).unwrap();
    }
    let mut events = String::from("h\nk");
    for k in &keys {
        write!(events, " {k}").unwrap();
    }
    events.push('\n');
    for &k in &keys {
        let base = draw(rng);
        // Mostly unchanged, so that every rule is reached.
        let parent_body = if rng.chance(50) { base } else { draw(rng) };
        let child_body = if rng.chance(40) { base } else { draw(rng) };
        reached.insert(
            match (
                child_body == base,
                parent_body == base,
                parent_body == child_body,
            ) {
                (true, _, _) => Case::Kept,
                (false, true, _) if child_body.is_none() => Case::TakenRemoval,
                (false, true, _) => Case::Taken,
                (false, false, true) => Case::Same,
                (false, false, false) if parent_body.is_none() || child_body.is_none() => {
                    Case::RemovalConflict
                }
                (false, false, false) => Case::Conflict,
            },
        );
        for (letter, side, body) in [
            ('p', parent.clone(), parent_body),
            ('b', root.join(BASE), base),
            ('c', root.join(TREE), child_body),
        ] {
            if let Some(v) = body {
                writeln!(events, "{letter} {k} {v}").unwrap();
                fs::write(side.join(name(k)), v.to_string()).unwrap();
            }
        }
    }
    write_json(
        &root.join(MANIFEST),
        &Manifest {
            parent: parent.clone(),
            copy: CopyReport {
                files: 0,
                cloned: 0,
                copied: 0,
            },
        },
    )
    .unwrap();
    let handback = hand_back_at(&root).unwrap();
    let mut transcript = String::from("w");
    for &k in &keys {
        if let Some(v) = read(&parent.join(name(k))) {
            write!(transcript, " {k}:{v}").unwrap();
        }
    }
    transcript.push_str("\nc");
    for conflict in &handback.conflicts {
        let k: u64 = conflict.trim_start_matches('f').parse().unwrap();
        write!(transcript, " {k}").unwrap();
    }
    transcript.push('\n');
    (events, transcript)
}

/// The content of the file at `path`, or none.
fn read(path: &Path) -> Option<String> {
    match fs::read_to_string(path) {
        Ok(text) => Some(text),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => panic!("cannot read {}: {error}", path.display()),
    }
}

#[test]
fn the_rust_hand_back_equals_the_bend_model() {
    let mut rng = Rng(0x0c0e_5a4d_b0c5_0003);
    let mut reached = BTreeSet::new();
    let scenarios: Vec<Scenario> = (0..200)
        .map(|at| {
            let (events, transcript) = scenario(&mut rng, &mut reached);
            Scenario {
                name: format!("hand-back {at}"),
                events,
                transcript,
            }
        })
        .collect();
    compare("bend/bridge_sandbox.bend", scenarios);
    // The scenarios reach every rule of the model.
    assert_eq!(
        reached,
        BTreeSet::from([
            Case::Kept,
            Case::Taken,
            Case::TakenRemoval,
            Case::Same,
            Case::Conflict,
            Case::RemovalConflict,
        ])
    );
}
