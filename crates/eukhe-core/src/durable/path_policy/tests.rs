use std::path::PathBuf;
use std::sync::atomic::AtomicU64;

use eukhe_docs::{Access, Documents, WriteError};
use eukhe_types::path_policy::{resolve, PathClass};
use eukhe_types::shell::{AutoSet, ShellEffect};

use super::*;

/// Regression (audit C2): every file the settings loaders read, and the
/// auth store, is Protected or Secret, so no agent write to it runs
/// without the user's yes, whatever `shell.autoEffects` holds.
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
    let auto = AutoSet::new(ShellEffect::ALL);
    let unasked: Vec<(PathBuf, bool)> = files
        .iter()
        .map(|file| {
            (
                file.clone(),
                auto.allows(effects(&policy, Access::Write, &resolve(file))),
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
    assert_eq!(
        [
            policy.class(&agent_dir.join("auth.json")),
            policy.class(&home.join(".ssh/id_ed25519")),
            policy.class(&cwd.join("src/main.rs")),
            policy.class(&top.join("elsewhere.txt")),
        ],
        [
            PathClass::Secret,
            PathClass::Secret,
            PathClass::Inside,
            PathClass::Outside
        ]
    );
}

/// Regression (G1 bridge): `ws/a/../x` where the link `a` loops resolves
/// to `ws/x` with no link left, but its links looped, so its class is
/// Outside (`laws/path_policy.bend`, `Pp.class`). The gate judged a second
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
    };
    let locks = tempfile::tempdir().unwrap();
    let written = Documents::new(locks.path().to_path_buf(), None)
        .write(&ws, "a/../x", "text", &gate)
        .map(|outcome| outcome.bytes)
        .map_err(|error| match error {
            WriteError::Refused { reason, .. } => reason,
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
user to attach a client, or to allow its effect in shell.autoEffects if that is write, exec or \
net; or use read-only steps."
                    .to_owned()
            ),
            false
        )
    );
}
