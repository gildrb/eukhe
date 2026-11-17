use std::path::PathBuf;
use std::sync::atomic::AtomicU64;

use eukhe_docs::{Access, Documents, WriteError};
use eukhe_types::path_policy::{resolve, PathClass};
use eukhe_types::shell::{AutoSet, ShellEffect};

use super::*;

/// Regression (audit C2): every file the settings loaders read, and the
/// auth store, is Protected or Secret, so for a user whose auto set
/// lacks the file's effect no agent write to it runs without the user's
/// yes.
#[test]
fn every_loader_file_is_guarded_and_a_project_file_is_inside() {
    let dir = tempfile::tempdir().unwrap();
    let top = dir.path().canonicalize().unwrap();
    let (home, agent_dir, cwd) = (top.join("home"), top.join("home/.eukhe"), top.join("work"));
    std::fs::create_dir_all(&agent_dir).unwrap();
    let settings = EukheSettings::new(&cwd, &agent_dir);
    std::fs::create_dir_all(cwd.join("src")).unwrap();
    let policy = policy(
        &Layout {
            agent_dir: &agent_dir,
            settings: &settings,
            home: Some(&home),
            executable: None,
            path: None,
            env: &|_| None,
        },
        &cwd,
    );
    let mut files: Vec<PathBuf> = settings.watched().to_vec();
    files.extend([
        agent_dir.join("models.json"),
        agent_dir.join("binds.cfg"),
        agent_dir.join("agents/other.cfg"),
        cwd.join(".git/hooks/pre-commit"),
        cwd.join("sub/.eukhe/settings.json"),
    ]);
    let auto = AutoSet::new([
        ShellEffect::Read,
        ShellEffect::Write,
        ShellEffect::Exec,
        ShellEffect::Net,
        ShellEffect::Outside,
    ]);
    let unasked: Vec<(PathBuf, bool)> = files
        .iter()
        .map(|file| {
            (
                file.clone(),
                eukhe_bend::rules::shell::allows(
                    auto,
                    effects(&policy, Access::Write, &resolve(file)),
                ) == eukhe_bend::rules::shell::Gate::Unasked,
            )
        })
        .collect();
    assert_eq!(
        unasked,
        files
            .iter()
            .map(|file| (file.clone(), false))
            .collect::<Vec<_>>()
    );
    // The fixture world lives in the OS temp dir, a workspace root: a path
    // beside the workspace inside it is Inside; one outside both roots is Outside.
    assert_eq!(
        [
            eukhe_shell::paths::judge_path(&policy, &agent_dir.join("auth.json")).class,
            eukhe_shell::paths::judge_path(&policy, &home.join(".ssh/id_ed25519")).class,
            eukhe_shell::paths::judge_path(&policy, &cwd.join("src/main.rs")).class,
            eukhe_shell::paths::judge_path(&policy, &top.join("elsewhere.txt")).class,
            eukhe_shell::paths::judge_path(&policy, std::path::Path::new("/elsewhere.txt")).class,
        ],
        [
            PathClass::Secret,
            PathClass::Secret,
            PathClass::Inside,
            PathClass::Inside,
            PathClass::Outside
        ]
    );
}

/// Every part of the state list is Protected or Secret: the run dir and
/// the auto-start dirs with everything under them, the work root and its
/// entries, the credentials.
#[test]
fn every_state_part_is_protected_or_secret() {
    let dir = tempfile::tempdir().unwrap();
    let top = dir.path().canonicalize().unwrap();
    let (home, agent_dir, cwd) = (top.join("home"), top.join("home/.eukhe"), top.join("work"));
    std::fs::create_dir_all(&agent_dir).unwrap();
    let settings = EukheSettings::new(&cwd, &agent_dir);
    let executable = top.join("bin/eukhe");
    let policy = policy(
        &Layout {
            agent_dir: &agent_dir,
            settings: &settings,
            home: Some(&home),
            executable: Some(&executable),
            path: None,
            env: &|_| None,
        },
        &cwd,
    );
    let class = |path: &Path| eukhe_shell::paths::judge_path(&policy, path).class;
    let work_root = top.join("home/.eukhe-work");
    assert_eq!(
        [
            class(&agent_dir.join("run/daemon.sock")),
            class(&agent_dir.join("dashboard-token")),
            class(&home.join(".aws/credentials")),
            class(&work_root.join("workspaces")),
            class(&top.join("bin/eukhe")),
        ],
        [
            PathClass::Protected,
            PathClass::Secret,
            PathClass::Secret,
            PathClass::Protected,
            PathClass::Protected,
        ]
    );
}

/// Regression (G1 bridge): `ws/a/../x` where the link `a` loops resolves
/// to `ws/x` with no link left, but its links looped, so its class is
/// Outside (`laws/path_policy/policy.bend`, `Pp.class`). The gate judged a second
/// resolution of `ws/x`, which lost the loop: the write ran unasked as
/// Inside.
#[test]
fn a_write_whose_links_looped_asks_even_when_its_real_path_is_inside() {
    let dir = tempfile::tempdir().unwrap();
    let ws = dir.path().canonicalize().unwrap();
    std::os::unix::fs::symlink("a", ws.join("a")).unwrap();
    let runtime = tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap();
    let gate = DocumentsGate {
        policy: PathPolicy::new(vec![ws.clone()], Vec::new(), Vec::new()),
        auto: AutoSet::new([ShellEffect::Read, ShellEffect::Write]),
        sink: None,
        call: "call".to_owned(),
        asked: AtomicU64::new(0),
        runtime: runtime.handle().clone(),
        held: Vec::new(),
    };
    let locks = tempfile::tempdir().unwrap();
    let written = Documents::new(locks.path().to_path_buf(), None)
        .write(&ws, "a/../x", "text", &gate, &eukhe_docs::Unwitnessed)
        .map(|outcome| outcome.bytes)
        .map_err(|error| match error {
            WriteError::Refused { reason, .. } => reason.to_string(),
            WriteError::IsDirectory { .. }
            | WriteError::Changed { .. }
            | WriteError::Unseen { .. }
            | WriteError::Io { .. } => error.to_string(),
        });
    assert_eq!(
        (written, ws.join("x").exists()),
        (
            Err(
                "(write+outside) it needs the user's approval, and no client answered. Ask the \
user to attach a client, or to allow its effect in shell.autoEffects if that is read, write, \
exec, net, outside, protected or secret; or \
use read-only steps."
                    .to_owned()
            ),
            false
        )
    );
}

/// A file an acceptance check protects belongs to the task's owner: the
/// worker's documents write to it is refused even when the user's auto set
/// lets workspace writes run, and the file keeps its bytes; another file of
/// the workspace is written as before.
#[test]
fn a_write_to_a_file_a_check_protects_is_refused() {
    let dir = tempfile::tempdir().unwrap();
    let ws = dir.path().canonicalize().unwrap();
    std::fs::write(ws.join("LAWS.bend"), "law a:\n").unwrap();
    let runtime = tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap();
    let gate = DocumentsGate {
        policy: PathPolicy::new(vec![ws.clone()], Vec::new(), Vec::new()),
        auto: AutoSet::new([ShellEffect::Read, ShellEffect::Write]),
        sink: None,
        call: "call".to_owned(),
        asked: AtomicU64::new(0),
        runtime: runtime.handle().clone(),
        held: vec![HeldFile {
            real: ws.join("LAWS.bend"),
            named: "LAWS.bend".to_owned(),
            check: 1,
        }],
    };
    let locks = tempfile::tempdir().unwrap();
    let documents = Documents::new(locks.path().to_path_buf(), None);
    let written = documents
        .write(&ws, "LAWS.bend", "", &gate, &eukhe_docs::Unwitnessed)
        .map(|outcome| outcome.bytes)
        .map_err(|error| match error {
            WriteError::Refused { reason, .. } => reason.to_string(),
            WriteError::IsDirectory { .. }
            | WriteError::Changed { .. }
            | WriteError::Unseen { .. }
            | WriteError::Io { .. } => error.to_string(),
        });
    assert_eq!(
        (written, std::fs::read_to_string(ws.join("LAWS.bend")).unwrap()),
        (
            Err("(write protected) LAWS.bend belongs to acceptance check 1: only the task's owner changes it".to_owned()),
            "law a:\n".to_owned()
        )
    );
    // Another file of the workspace is written as before.
    assert!(documents
        .write(&ws, "notes.txt", "text", &gate, &eukhe_docs::Unwitnessed)
        .is_ok());
}
