use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use eukhe_durable::harness::effects::EffectsState;
use eukhe_types::effects::{EffectClass, RanEffect, RanKind};
use eukhe_types::undo::DiffScope;

use super::store::FILE_CAP_BYTES;
use super::{prune_snapshots, snapshots_dir, TurnSnapshots, UndoError, UndoReply};

/// A ledger with no irreversible effect.
fn ledger() -> EffectsState {
    EffectsState::default()
}

/// What a path of the workspace is: a file's bytes and executable bit, or
/// a symlink's target.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Node {
    File(Vec<u8>, bool),
    Link(PathBuf),
}

/// Every file and symlink under `root` but `.git`, by relative path.
fn tree(root: &Path) -> BTreeMap<String, Node> {
    fn walk(root: &Path, dir: &Path, out: &mut BTreeMap<String, Node>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            let rel = path
                .strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .into_owned();
            if rel == ".git" {
                continue;
            }
            let meta = std::fs::symlink_metadata(&path).unwrap();
            if meta.file_type().is_symlink() {
                out.insert(rel, Node::Link(std::fs::read_link(&path).unwrap()));
            } else if meta.is_dir() {
                walk(root, &path, out);
            } else {
                let exec =
                    std::os::unix::fs::PermissionsExt::mode(&meta.permissions()) & 0o111 != 0;
                out.insert(rel, Node::File(std::fs::read(&path).unwrap(), exec));
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(root, root, &mut out);
    out
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap()
}

fn write(root: &Path, path: &str, bytes: &[u8]) {
    let full = root.join(path);
    std::fs::create_dir_all(full.parent().unwrap()).unwrap();
    std::fs::write(full, bytes).unwrap();
}

fn link(root: &Path, path: &str, target: &str) {
    let full = root.join(path);
    let _ = std::fs::remove_file(&full);
    std::os::unix::fs::symlink(target, full).unwrap();
}

struct Fixture {
    _dir: tempfile::TempDir,
    agent: PathBuf,
    workspace: PathBuf,
    snapshots: TurnSnapshots,
}

fn fixture() -> Fixture {
    let dir = tempfile::tempdir().unwrap();
    let agent = dir.path().join("agent");
    let workspace = dir.path().join("ws");
    std::fs::create_dir_all(&workspace).unwrap();
    let snapshots = TurnSnapshots::open(&agent, "s1", &workspace).unwrap();
    Fixture {
        _dir: dir,
        agent,
        workspace,
        snapshots,
    }
}

/// The workspace a turn starts on: a plain file, a file the turn
/// changes, one it removes, a binary file, an executable, a symlink, a
/// file in a directory, and an ignored file.
fn seed(ws: &Path) {
    write(ws, ".gitignore", b"*.log\n");
    write(ws, "keep.txt", b"keep\n");
    write(ws, "mod.txt", b"one\n");
    write(ws, "gone.txt", b"gone\n");
    write(ws, "bin.dat", &[0, 1, 2, 255, 0]);
    write(ws, "run.sh", b"#!/bin/sh\n");
    std::fs::set_permissions(
        ws.join("run.sh"),
        std::os::unix::fs::PermissionsExt::from_mode(0o755),
    )
    .unwrap();
    link(ws, "link", "keep.txt");
    write(ws, "dir/inner.txt", b"inner\n");
    write(ws, "noise.log", b"before\n");
}

/// The turn's work: every kind of change, the ignored file included.
fn work(ws: &Path) {
    write(ws, "mod.txt", b"two\n");
    std::fs::remove_file(ws.join("gone.txt")).unwrap();
    write(ws, "new/added.txt", b"added\n");
    write(ws, "bin.dat", &[9, 9, 0]);
    std::fs::set_permissions(
        ws.join("run.sh"),
        std::os::unix::fs::PermissionsExt::from_mode(0o644),
    )
    .unwrap();
    link(ws, "link", "mod.txt");
    std::fs::remove_file(ws.join("dir/inner.txt")).unwrap();
    std::fs::remove_dir(ws.join("dir")).unwrap();
    write(ws, "noise.log", b"after\n");
}

const CHANGED: [&str; 7] = [
    "bin.dat",
    "dir/inner.txt",
    "gone.txt",
    "link",
    "mod.txt",
    "new/added.txt",
    "run.sh",
];

fn names(paths: &[&str]) -> Vec<String> {
    paths.iter().map(|path| (*path).to_owned()).collect()
}

/// Undo of one turn in a directory that is no git repository: every
/// added, removed, modified, binary, executable and symlinked path is back
/// as it was; the ignored file keeps the turn's content; /diff listed the
/// same paths before.
#[tokio::test]
async fn undo_restores_a_plain_directory() {
    let f = fixture();
    seed(&f.workspace);
    let before = tree(&f.workspace);
    assert_eq!(f.snapshots.take_turn(1).await.unwrap(), 1);
    work(&f.workspace);
    let diff = f.snapshots.diff(DiffScope::Turn).await.unwrap();
    assert_eq!(
        (diff.paths, diff.skipped, diff.diff.contains("-one\n+two\n")),
        (names(&CHANGED), Vec::new(), true)
    );
    let reply = f.snapshots.undo(&ledger()).await.unwrap();
    let mut expected = before;
    expected.insert(
        "noise.log".to_owned(),
        Node::File(b"after\n".to_vec(), false),
    );
    assert_eq!(
        (reply, tree(&f.workspace)),
        (
            UndoReply {
                restored: names(&CHANGED),
                turn: 1,
                left: 0,
                not_undone: Vec::new(),
            },
            expected
        )
    );
    assert!(matches!(
        f.snapshots.undo(&ledger()).await,
        Err(UndoError::NothingToUndo)
    ));
}

/// In a git repository the workspace's own `.git` is never snapshotted
/// nor touched, and a nested repository is held back.
#[tokio::test]
async fn undo_keeps_the_repository_and_nested_ones() {
    let f = fixture();
    let git = |dir: &Path| {
        let status = std::process::Command::new("git")
            .args(["init", "-q"])
            .current_dir(dir)
            .status()
            .unwrap();
        assert!(status.success());
    };
    git(&f.workspace);
    seed(&f.workspace);
    write(&f.workspace, "sub/x.txt", b"x\n");
    git(&f.workspace.join("sub"));
    let head = std::fs::read(f.workspace.join(".git/HEAD")).unwrap();
    f.snapshots.take_turn(1).await.unwrap();
    work(&f.workspace);
    write(&f.workspace, "sub/x.txt", b"y\n");
    let diff = f.snapshots.diff(DiffScope::Turn).await.unwrap();
    assert_eq!(
        (diff.paths, diff.skipped),
        (names(&CHANGED), names(&["sub/"]))
    );
    f.snapshots.undo(&ledger()).await.unwrap();
    assert_eq!(
        (
            std::fs::read(f.workspace.join(".git/HEAD")).unwrap(),
            std::fs::read(f.workspace.join("sub/x.txt")).unwrap(),
            std::fs::read(f.workspace.join("mod.txt")).unwrap(),
        ),
        (head, b"y\n".to_vec(), b"one\n".to_vec())
    );
}

/// A file over the size cap is held back: /diff names it skipped, /undo
/// leaves it, even when the turn shrank it below the cap.
#[tokio::test]
async fn a_file_over_the_cap_is_never_touched() {
    let f = fixture();
    let big = vec![b'a'; usize::try_from(FILE_CAP_BYTES).unwrap() + 1];
    write(&f.workspace, "big.bin", &big);
    write(&f.workspace, "small.txt", b"small\n");
    f.snapshots.take_turn(1).await.unwrap();
    write(&f.workspace, "big.bin", b"now small\n");
    write(&f.workspace, "small.txt", b"changed\n");
    let diff = f.snapshots.diff(DiffScope::Turn).await.unwrap();
    assert_eq!(
        (diff.paths, diff.skipped),
        (names(&["small.txt"]), names(&["big.bin"]))
    );
    f.snapshots.undo(&ledger()).await.unwrap();
    assert_eq!(
        (
            std::fs::read(f.workspace.join("big.bin")).unwrap(),
            std::fs::read(f.workspace.join("small.txt")).unwrap()
        ),
        (b"now small\n".to_vec(), b"small\n".to_vec())
    );
}

/// Two turns: /diff shows the second's change, /diff all both; two /undo
/// restore the start; a third is refused; a turn after an undo stands on
/// what is left.
#[tokio::test]
async fn undo_walks_back_the_turns() {
    let f = fixture();
    write(&f.workspace, "a.txt", b"0\n");
    f.snapshots.take_turn(1).await.unwrap();
    write(&f.workspace, "a.txt", b"1\n");
    f.snapshots.take_turn(2).await.unwrap();
    write(&f.workspace, "b.txt", b"2\n");
    let (turn, all) = (
        f.snapshots.diff(DiffScope::Turn).await.unwrap().paths,
        f.snapshots.diff(DiffScope::All).await.unwrap().paths,
    );
    assert_eq!((turn, all), (names(&["b.txt"]), names(&["a.txt", "b.txt"])));
    let first = f.snapshots.undo(&ledger()).await.unwrap();
    // A turn after the undo: its snapshot replaces the undone one.
    write(&f.workspace, "c.txt", b"3\n");
    assert_eq!(f.snapshots.take_turn(3).await.unwrap(), 2);
    write(&f.workspace, "a.txt", b"4\n");
    let second = f.snapshots.undo(&ledger()).await.unwrap();
    let third = f.snapshots.undo(&ledger()).await.unwrap();
    assert_eq!(
        (
            (first.turn, first.restored, first.left),
            (second.turn, second.restored, second.left),
            (third.turn, third.restored, third.left),
            tree(&f.workspace),
        ),
        (
            (2, names(&["b.txt"]), 1),
            (2, names(&["a.txt"]), 1),
            (1, names(&["a.txt", "c.txt"]), 0),
            BTreeMap::from([("a.txt".to_owned(), Node::File(b"0\n".to_vec(), false))]),
        )
    );
    assert!(matches!(
        f.snapshots.undo(&ledger()).await,
        Err(UndoError::NothingToUndo)
    ));
}

/// Each /undo names the irreversible effects of the undone prompt's run,
/// in ledger order, and none of another run's: they ran and stay.
#[tokio::test]
async fn undo_names_the_irreversible_effects_of_the_undone_run() {
    let f = fixture();
    let effect = |id: &str, run: u64, command: &str| RanEffect {
        id: id.to_owned(),
        key: format!("s1:{id}"),
        run,
        kind: RanKind::ShellStep,
        command: command.to_owned(),
        classes: vec![EffectClass::Net],
        agent: None,
        session_id: "s1".to_owned(),
        at_ms: 0,
    };
    let ran = vec![
        effect("e1", 4, "git push origin a"),
        effect("e2", 5, "git push origin b"),
        effect("e3", 4, "curl -X POST https://x"),
    ];
    let ledger = EffectsState {
        run: 5,
        ran: ran.clone(),
        ..EffectsState::default()
    };
    write(&f.workspace, "a.txt", b"0\n");
    f.snapshots.take_turn(4).await.unwrap();
    write(&f.workspace, "a.txt", b"1\n");
    f.snapshots.take_turn(5).await.unwrap();
    write(&f.workspace, "a.txt", b"2\n");
    let second = f.snapshots.undo(&ledger).await.unwrap().not_undone;
    let first = f.snapshots.undo(&ledger).await.unwrap().not_undone;
    assert_eq!(
        (second, first),
        (vec![ran[1].clone()], vec![ran[0].clone(), ran[2].clone()])
    );
}

/// Before any turn there is nothing to compare with or to undo.
#[tokio::test]
async fn nothing_before_the_first_turn() {
    let f = fixture();
    assert!(matches!(
        (
            f.snapshots.diff(DiffScope::All).await,
            f.snapshots.undo(&ledger()).await
        ),
        (Err(UndoError::NothingToDiff), Err(UndoError::NothingToUndo))
    ));
}

/// The turn starting while the shadow index is locked: its snapshot
/// fails.
async fn failed_turn(f: &Fixture) -> UndoError {
    let git_dir = snapshots_dir(&f.agent).unwrap().join("s1.git");
    std::fs::create_dir_all(&git_dir).unwrap();
    let lock = git_dir.join("index.lock");
    std::fs::write(&lock, b"").unwrap();
    let error = f.snapshots.take_turn(1).await.unwrap_err();
    std::fs::remove_file(&lock).unwrap();
    error
}

/// The reason a lost turn keeps: the first line of why its snapshot
/// failed.
fn kept_reason(error: &UndoError) -> String {
    error
        .to_string()
        .lines()
        .next()
        .unwrap_or_default()
        .trim()
        .to_owned()
}

/// A turn whose snapshot failed still counts: /undo takes back the turns
/// after it, then stops at its start, refused with why and changing
/// nothing, every time; it never takes back two turns at once. /diff of
/// that turn is refused alike; /diff all still answers.
#[tokio::test]
async fn undo_stops_at_a_turn_without_a_snapshot() {
    let f = fixture();
    write(&f.workspace, "a.txt", b"0\n");
    f.snapshots.take_turn(1).await.unwrap();
    write(&f.workspace, "a.txt", b"1\n");
    let failed = failed_turn(&f).await;
    write(&f.workspace, "a.txt", b"2\n");
    assert_eq!(f.snapshots.take_turn(3).await.unwrap(), 3);
    write(&f.workspace, "a.txt", b"3\n");
    let back = f.snapshots.undo(&ledger()).await.unwrap();
    let at_two = read(&f.workspace.join("a.txt"));
    let stop = f.snapshots.undo(&ledger()).await.unwrap_err();
    let again = f.snapshots.undo(&ledger()).await.unwrap_err();
    let turn = f.snapshots.diff(DiffScope::Turn).await.unwrap_err();
    let all = f.snapshots.diff(DiffScope::All).await.unwrap().paths;
    let reason = kept_reason(&failed);
    let refused = |error: &UndoError| match error {
        UndoError::NoTurnSnapshot { turn, reason } => Some((*turn, reason.clone())),
        _ => None,
    };
    assert_eq!(
        (
            (back.turn, back.restored, back.left),
            at_two,
            refused(&stop),
            refused(&again),
            refused(&turn),
            all,
            read(&f.workspace.join("a.txt")),
        ),
        (
            (3, names(&["a.txt"]), 0),
            "2\n".to_owned(),
            Some((2, reason.clone())),
            Some((2, reason.clone())),
            Some((2, reason)),
            names(&["a.txt"]),
            "2\n".to_owned(),
        )
    );
    assert_eq!(
        stop.to_string(),
        format!(
            "Prompt 2 has no workspace snapshot (taking it failed: {}), so /undo and /diff cannot go back past its start; nothing changed",
            kept_reason(&failed)
        )
    );
}

/// The session's first turn without a snapshot is where /diff all starts:
/// /diff all and the last /undo are refused for it, never answered from
/// a later turn's start.
#[tokio::test]
async fn a_first_turn_without_a_snapshot_is_where_diff_all_starts() {
    let f = fixture();
    write(&f.workspace, "a.txt", b"0\n");
    let failed = failed_turn(&f).await;
    write(&f.workspace, "a.txt", b"1\n");
    assert_eq!(f.snapshots.take_turn(2).await.unwrap(), 2);
    write(&f.workspace, "a.txt", b"2\n");
    let all = f.snapshots.diff(DiffScope::All).await.unwrap_err();
    let back = f.snapshots.undo(&ledger()).await.unwrap();
    let stop = f.snapshots.undo(&ledger()).await.unwrap_err();
    let reason = kept_reason(&failed);
    let refused = |error: &UndoError| match error {
        UndoError::NoTurnSnapshot { turn, reason } => Some((*turn, reason.clone())),
        _ => None,
    };
    assert_eq!(
        (
            refused(&all),
            (back.turn, back.left),
            refused(&stop),
            read(&f.workspace.join("a.txt")),
        ),
        (
            Some((1, reason.clone())),
            (2, 0),
            Some((1, reason)),
            "1\n".to_owned(),
        )
    );
}

/// A turn start that cannot even read the store: from then on every
/// turn, /undo and /diff is refused as unread, so no /undo ever restores
/// an older turn's start in place of the lost one.
#[tokio::test]
async fn an_unread_store_refuses_every_undo() {
    let f = fixture();
    write(&f.workspace, "a.txt", b"0\n");
    f.snapshots.take_turn(1).await.unwrap();
    let head = snapshots_dir(&f.agent).unwrap().join("s1.git/HEAD");
    let kept = std::fs::read(&head).unwrap();
    std::fs::write(&head, b"not a ref\n").unwrap();
    assert!(f.snapshots.take_turn(2).await.is_err());
    std::fs::write(&head, kept).unwrap();
    write(&f.workspace, "a.txt", b"1\n");
    assert!(matches!(
        (
            f.snapshots.take_turn(3).await,
            f.snapshots.undo(&ledger()).await,
            f.snapshots.diff(DiffScope::All).await,
        ),
        (
            Err(UndoError::Unread { .. }),
            Err(UndoError::Unread { .. }),
            Err(UndoError::Unread { .. }),
        )
    ));
    assert_eq!(read(&f.workspace.join("a.txt")), "1\n");
}

/// Old sessions' snapshots go; the running session's and recent ones stay.
#[test]
fn prune_removes_only_old_sessions() {
    let f = fixture();
    let dir = snapshots_dir(&f.agent).unwrap();
    for name in ["old.git", "recent.git", "s1.git"] {
        std::fs::create_dir_all(dir.join(name)).unwrap();
    }
    let removed_now = prune_snapshots(&dir, 2, SystemTime::now(), "s1").unwrap();
    let later = SystemTime::now() + Duration::from_hours(3 * 24);
    let removed_late = prune_snapshots(&dir, 2, later, "s1").unwrap();
    let left: Vec<String> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    assert_eq!(
        (removed_now, removed_late, left),
        (
            Vec::<String>::new(),
            names(&["old.git", "recent.git"]),
            names(&["s1.git"])
        )
    );
}
