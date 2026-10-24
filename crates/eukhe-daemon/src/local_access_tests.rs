//! The IO around the local access decisions, which run as the compiled
//! core (`eukhe_bend::rules::fsmode`, laws `laws/fsmode.bend`): what the
//! socket-dir check and the session cwd check read from the filesystem,
//! and the modes the real creation paths give every dir and file under a
//! fresh home.

use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};

use eukhe_bend::rules::fsmode::{made_mode, Made};

use crate::platform::{prepare_socket_dir, SocketDir};
use crate::session_cwd::{session_cwd, CwdError};

/// The socket-dir check on real dirs: a missing dir is created 0700 and
/// used; a 0755 dir is used; a 0720 dir, a link to a 0700 dir, a file and
/// a dir another uid owns are refused, each error naming what was found.
#[test]
fn the_socket_dir_check_reads_the_dir_it_judges() {
    let home = tempfile::tempdir().unwrap();
    let dir = |name: &str, mode: u32| {
        let path = home.path().join(name);
        std::fs::create_dir(&path).unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(mode)).unwrap();
        path
    };
    let missing = home.path().join("run").join("sockets");
    let open = dir("open", 0o755);
    let writable = dir("writable", 0o720);
    let private = dir("private", 0o700);
    let link = home.path().join("link");
    std::os::unix::fs::symlink(&private, &link).unwrap();
    let file = home.path().join("file");
    std::fs::write(&file, "").unwrap();
    let refusal = |path: &Path| prepare_socket_dir(path).unwrap_err().to_string();
    assert_eq!(
        (
            prepare_socket_dir(&missing).unwrap(),
            std::fs::metadata(&missing).unwrap().mode() & 0o777,
            prepare_socket_dir(&open).unwrap(),
        ),
        (SocketDir::Created, 0o700, SocketDir::Used)
    );
    assert!(refusal(&writable).contains("has mode 0720"));
    assert!(refusal(&link).contains("is a symbolic link"));
    assert!(refusal(&file).contains("is not a directory"));
    // `/` is root's: a dir another uid owns (unless the tests run as root).
    if eukhe_types::platform::access::current_uid() != 0 {
        assert!(refusal(Path::new("/")).contains("is owned by uid 0"));
    }
}

/// The cwd check on real paths: none, an empty one, a missing path, a
/// file and a dir.
#[test]
fn the_cwd_check_reads_the_path_it_judges() {
    let home = tempfile::tempdir().unwrap();
    let missing = home.path().join("missing");
    let file = home.path().join("file");
    std::fs::write(&file, "").unwrap();
    let text = |path: &Path| path.display().to_string();
    assert_eq!(
        [
            session_cwd(None),
            session_cwd(Some("")),
            session_cwd(Some(&text(&missing))),
            session_cwd(Some(&text(&file))),
            session_cwd(Some(&text(home.path()))),
        ],
        [
            Err(CwdError::Missing),
            Err(CwdError::Missing),
            Err(CwdError::Gone(missing.clone())),
            Err(CwdError::NotADirectory(file.clone())),
            Ok(home.path().to_path_buf()),
        ]
    );
}

/// Every dir and file under `root` (`root` included), sorted.
fn walk(root: &Path) -> Vec<PathBuf> {
    let mut found = vec![root.to_path_buf()];
    let mut pending = vec![root.to_path_buf()];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if std::fs::symlink_metadata(&path).unwrap().is_dir() {
                pending.push(path.clone());
            }
            found.push(path);
        }
    }
    found.sort();
    found
}

/// The entries under `root` whose mode is not the core's for their kind.
fn off_mode(root: &Path) -> Vec<(PathBuf, u32)> {
    let (dir_mode, file_mode) = (made_mode(Made::Dir), made_mode(Made::File));
    walk(root)
        .into_iter()
        .filter_map(|path| {
            let found = std::fs::symlink_metadata(&path).unwrap();
            let mode = found.mode() & 0o777;
            let want = if found.is_dir() { dir_mode } else { file_mode };
            (mode != want).then_some((path, mode))
        })
        .collect()
}

/// The real creation paths (the daemon's start dirs, the socket dir, the
/// auth store, a worker's session, a legacy import and a fork) give every
/// dir and file the core's mode: 0700 a dir, 0600 a file.
#[tokio::test(flavor = "multi_thread")]
async fn every_creation_path_makes_the_core_modes() {
    let home = tempfile::tempdir().unwrap();
    let agent = home.path().join("agent");
    crate::paths::ensure_dir(&agent.join("sessions")).unwrap();
    prepare_socket_dir(&home.path().join("run").join("eukhe-sockets")).unwrap();

    let auth_agent = home.path().join("auth-agent");
    eukhe_core::auth::AuthStorage::create(&auth_agent)
        .set(
            "faux",
            eukhe_core::auth::AuthCredential::ApiKey {
                key: "sk-local".to_string(),
                prime_team: None,
            },
        )
        .expect("the auth store writes");

    let (worker_dir, _worker) =
        crate::durable_test_support::created_worker("local-access", serde_json::json!([])).await;
    let mut legacy = crate::session_store::SessionFile::create("/work", None, 0);
    legacy.append_message(&serde_json::json!({
        "role": "user", "content": "hi", "timestamp": 1u64
    }));
    let legacy_path = home.path().join("legacy.jsonl");
    legacy.set_path(legacy_path.clone());
    legacy.rewrite().unwrap();
    let store = home.path().join("store");
    let imported = store.join("sessions").join("imported");
    let cx = eukhe_chord::context::BACKGROUND_CONTEXT.clone();
    eukhe_core::durable::import_legacy_session(&legacy_path, &imported, &cx)
        .await
        .unwrap();
    eukhe_core::durable::fork_session(
        &eukhe_core::durable::SessionLocation::Durable(imported),
        eukhe_core::durable::ForkPoint::Latest,
        /*cwd*/ None,
        &store.join("sessions").join("forked"),
        &cx,
    )
    .await
    .unwrap();

    let roots = [
        agent,
        home.path().join("run"),
        auth_agent,
        worker_dir.path().join("agent"),
        store,
    ];
    let off: Vec<(PathBuf, u32)> = roots.iter().flat_map(|root| off_mode(root)).collect();
    assert_eq!(off, []);
}
