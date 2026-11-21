use std::path::PathBuf;

use eukhe_docs::{Access, Documents, WriteError};
use eukhe_types::path_policy::{resolve, OwnKind, PathClass};

use super::*;

/// Regression (audit C2): every file the settings loaders read, the
/// profiles and the session record are own: no agent writes them. A
/// file a check under acceptance protects is own too. A `.git` hook and
/// another project's `.eukhe` file are protected (a write there is
/// irreversible) but no agent is refused them.
#[test]
fn every_loader_file_and_the_session_record_are_own() {
    let dir = tempfile::tempdir().unwrap();
    let top = dir.path().canonicalize().unwrap();
    let (home, agent_dir, cwd) = (top.join("home"), top.join("home/.eukhe"), top.join("work"));
    std::fs::create_dir_all(&agent_dir).unwrap();
    let settings = EukheSettings::new(&cwd, &agent_dir);
    std::fs::create_dir_all(cwd.join("src")).unwrap();
    let protect = [cwd.join("tests/golden.txt")];
    let policy = policy(
        &Layout {
            agent_dir: &agent_dir,
            settings: &settings,
            home: Some(&home),
            executable: None,
            path: None,
            env: &|_| None,
            protect: &protect,
        },
        &cwd,
    );
    let own = |file: &Path| {
        eukhe_shell::paths::own_write(&policy, &resolve(file)).map(|written| written.kind)
    };
    let mut files: Vec<(PathBuf, Option<OwnKind>)> = settings
        .watched()
        .iter()
        .map(|file| (file.clone(), Some(OwnKind::Config)))
        .collect();
    files.extend([
        (agent_dir.join("models.json"), Some(OwnKind::Config)),
        (agent_dir.join("binds.cfg"), Some(OwnKind::Config)),
        (agent_dir.join("agents/other.cfg"), Some(OwnKind::Config)),
        (
            agent_dir.join("sessions/s1.jsonl"),
            Some(OwnKind::SessionRecord),
        ),
        (
            agent_dir.join("sessions-archive/s0.jsonl"),
            Some(OwnKind::SessionRecord),
        ),
        (cwd.join("tests/golden.txt"), Some(OwnKind::CheckFile)),
        (cwd.join(".git/hooks/pre-commit"), None),
        (cwd.join("sub/.eukhe/settings.json"), None),
        (cwd.join("src/main.rs"), None),
    ]);
    assert_eq!(
        files
            .iter()
            .map(|(file, _)| (file.clone(), own(file)))
            .collect::<Vec<_>>(),
        files
    );
    // The fixture world lives in the OS temp dir, a workspace root: a path
    // beside the workspace inside it is Inside; one outside both roots is Outside.
    assert_eq!(
        [
            eukhe_shell::paths::judge_path(&policy, &agent_dir.join("auth.json")).class,
            eukhe_shell::paths::judge_path(&policy, &home.join(".ssh/id_ed25519")).class,
            eukhe_shell::paths::judge_path(&policy, &cwd.join(".git/hooks/pre-commit")).class,
            eukhe_shell::paths::judge_path(&policy, &cwd.join("src/main.rs")).class,
            eukhe_shell::paths::judge_path(&policy, &top.join("elsewhere.txt")).class,
            eukhe_shell::paths::judge_path(&policy, std::path::Path::new("/elsewhere.txt")).class,
        ],
        [
            PathClass::Secret,
            PathClass::Secret,
            PathClass::Protected,
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
            protect: &[],
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
/// resolution of `ws/x`, which lost the loop: the write counted as
/// Inside, reversible.
#[test]
fn a_write_whose_links_looped_is_outside_even_when_its_real_path_is_inside() {
    let dir = tempfile::tempdir().unwrap();
    let ws = dir.path().canonicalize().unwrap();
    std::os::unix::fs::symlink("a", ws.join("a")).unwrap();
    let policy = PathPolicy::new(vec![ws.clone()], Vec::new(), Vec::new());
    assert_eq!(
        effects(&policy, Access::Write, &resolve(&ws.join("a/../x"))),
        ShellEffects::write_to(PathClass::Outside)
    );
}

/// A document tool's write to an own path is refused and names the path
/// and why; every other access runs.
#[test]
fn a_document_write_to_an_own_path_is_refused() {
    let dir = tempfile::tempdir().unwrap();
    let ws = dir.path().canonicalize().unwrap();
    let gate = DocumentsGate {
        policy: PathPolicy::new(vec![ws.clone()], Vec::new(), Vec::new()).with_own(vec![OwnRule {
            path: OwnPath::Tree(ws.join("own")),
            kind: OwnKind::Config,
        }]),
    };
    let locks = tempfile::tempdir().unwrap();
    let documents = Documents::new(locks.path().to_path_buf(), None);
    let write = |path: &str| {
        documents
            .write(&ws, path, "text", &gate, &eukhe_docs::Unwitnessed)
            .map(|outcome| outcome.bytes)
            .map_err(|error| match error {
                WriteError::Refused { reason, .. } => reason.to_string(),
                WriteError::IsDirectory { .. }
                | WriteError::Changed { .. }
                | WriteError::Unseen { .. }
                | WriteError::Io { .. } => error.to_string(),
            })
    };
    assert_eq!(
        (
            write("own/f"),
            write("note.txt"),
            ws.join("own/f").exists(),
            std::fs::read_to_string(ws.join("note.txt")).ok()
        ),
        (
            Err(format!(
                "(write) refused: {} is part of eukhe's own config and credentials; no agent may \
write it",
                ws.join("own/f").display()
            )),
            Ok(4),
            false,
            Some("text".to_owned())
        )
    );
}

/// A file an acceptance check protects belongs to the task's owner: the
/// worker's documents write to it is refused, and the file keeps its bytes;
/// another file of the workspace is written as before.
#[test]
fn a_write_to_a_file_a_check_protects_is_refused() {
    let dir = tempfile::tempdir().unwrap();
    let ws = dir.path().canonicalize().unwrap();
    std::fs::write(ws.join("LAWS.bend"), "law a:\n").unwrap();
    let gate = DocumentsGate {
        policy: PathPolicy::new(vec![ws.clone()], Vec::new(), Vec::new()).with_own(vec![OwnRule {
            path: OwnPath::Tree(ws.join("LAWS.bend")),
            kind: OwnKind::CheckFile,
        }]),
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
            Err(format!(
                "(write) refused: {} is part of the protected files of a check under \
acceptance; no agent may write it",
                ws.join("LAWS.bend").display()
            )),
            "law a:\n".to_owned()
        )
    );
    // Another file of the workspace is written as before.
    assert!(documents
        .write(&ws, "notes.txt", "text", &gate, &eukhe_docs::Unwitnessed)
        .is_ok());
}
