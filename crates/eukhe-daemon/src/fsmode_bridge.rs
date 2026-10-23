//! The bridge between the local access code and its Bend model
//! (`bend/fsmode.bend`, laws `LAWS.bend` section `fsmode`, proved in `PROOF.bend`):
//! both run the same scenarios and must print the same transcript, byte
//! for byte (`bridge/bridge_fsmode.bend` documents the format). Four kinds
//! of scenario, each on the real code:
//!
//! - socket dirs: missing dirs, dirs of this uid with generated modes, a
//!   link to a 0700 dir, a file, and system dirs another uid owns
//!   ([`crate::platform::prepare_socket_dir`]); the events are what
//!   `symlink_metadata` finds there.
//! - peers: generated uid pairs
//!   ([`eukhe_types::platform::access::peer_verdict`]).
//! - creations: every dir and file the real creation paths make under a
//!   fresh home ([`crate::paths::ensure_dir`], the socket dir, the auth
//!   store, a worker's session, a legacy import, a fork), walked and
//!   stat'ed; the model gives the mode of each.
//! - cwds: creates that name no cwd, an empty one, a missing path, a file
//!   and a dir ([`crate::session_cwd::session_cwd`]).
//!
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::platform::access::{
    current_uid, peer_verdict, PeerVerdict, GROUP_OTHER_WRITE_BITS,
};

use crate::platform::{prepare_socket_dir, SocketDir};
use crate::session_cwd::{session_cwd, CwdError};

/// The octal digits (user, group, other) of a mode.
fn digits(mode: u32) -> String {
    format!("{} {} {}", (mode >> 6) & 7, (mode >> 3) & 7, mode & 7)
}

/// One run of the real socket-dir check on `dir`: the event (what is
/// there) and the transcript line (what the check did).
fn socket_line(dir: &Path, events: &mut String, transcript: &mut String) {
    let (node, mine, loose) = match std::fs::symlink_metadata(dir) {
        Err(_) => ('m', true, false),
        Ok(found) => (
            if found.file_type().is_symlink() {
                'l'
            } else if found.is_dir() {
                'd'
            } else {
                'o'
            },
            found.uid() == current_uid(),
            found.mode() & GROUP_OTHER_WRITE_BITS != 0,
        ),
    };
    writeln!(events, "s {node} {} {}", u8::from(mine), u8::from(loose)).unwrap();
    let verdict = |dir: &Path| match prepare_socket_dir(dir) {
        Ok(SocketDir::Used) => "use".to_string(),
        Ok(SocketDir::Created) => "create".to_string(),
        Err(_) => "refuse".to_string(),
    };
    match prepare_socket_dir(dir) {
        Ok(SocketDir::Created) => {
            let mode = std::fs::metadata(dir).unwrap().mode() & 0o777;
            writeln!(transcript, "create {} then {}", digits(mode), verdict(dir)).unwrap();
        }
        Ok(SocketDir::Used) => transcript.push_str("use\n"),
        Err(_) => transcript.push_str("refuse\n"),
    }
}

/// The socket-dir scenario: `count` generated dirs in `base`, then the
/// system dirs another uid owns.
fn socket_scenario(rng: &mut Rng, base: &Path, count: u64) -> Scenario {
    const MODES: [u32; 10] = [
        0o700, 0o755, 0o750, 0o705, 0o720, 0o702, 0o770, 0o777, 0o500, 0o733,
    ];
    let (mut events, mut transcript) = (String::new(), String::new());
    for at in 0..count {
        let dir = base.join(format!("d{at}"));
        match rng.below(5) {
            0 => {}
            1 => {
                std::fs::create_dir(&dir).unwrap();
                let mode = rng.pick(&MODES).unwrap();
                std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(mode)).unwrap();
            }
            2 => {
                let target = base.join(format!("t{at}"));
                std::fs::create_dir(&target).unwrap();
                std::fs::set_permissions(&target, std::fs::Permissions::from_mode(0o700)).unwrap();
                std::os::unix::fs::symlink(&target, &dir).unwrap();
            }
            3 => std::fs::write(&dir, "not a dir").unwrap(),
            _ => {
                // A missing dir under missing parents: all are created.
                let dir = base.join(format!("p{at}")).join("nested");
                socket_line(&dir, &mut events, &mut transcript);
                continue;
            }
        }
        socket_line(&dir, &mut events, &mut transcript);
    }
    for system in ["/", "/root", "/usr"] {
        let dir = Path::new(system);
        if std::fs::symlink_metadata(dir).is_ok_and(|found| found.uid() != current_uid()) {
            socket_line(dir, &mut events, &mut transcript);
        }
    }
    Scenario {
        name: "socket dirs".to_string(),
        events,
        transcript,
    }
}

/// The peer scenario: generated uid pairs, half of them equal.
fn peer_scenario(rng: &mut Rng) -> Scenario {
    let (mut events, mut transcript) = (String::new(), String::new());
    for _ in 0..64 {
        let own = u32::try_from(rng.range(0, 3000)).unwrap();
        let peer = if rng.chance(50) {
            own
        } else {
            u32::try_from(rng.range(0, 3000)).unwrap()
        };
        writeln!(events, "p {peer} {own}").unwrap();
        transcript.push_str(match peer_verdict(peer, own) {
            PeerVerdict::Accept => "accept\n",
            PeerVerdict::Drop => "drop\n",
        });
    }
    Scenario {
        name: "peers".to_string(),
        events,
        transcript,
    }
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

/// The creation scenario of the tree at `root`: one event per entry, and
/// its real mode.
fn creation_scenario(name: &str, root: &Path) -> Scenario {
    let (mut events, mut transcript) = (String::new(), String::new());
    for path in walk(root) {
        let found = std::fs::symlink_metadata(&path).unwrap();
        let kind = if found.is_dir() { 'd' } else { 'f' };
        writeln!(events, "c {kind}").unwrap();
        writeln!(transcript, "made {kind} {}", digits(found.mode() & 0o777)).unwrap();
    }
    Scenario {
        name: format!("creations: {name}"),
        events,
        transcript,
    }
}

/// The cwd scenario: `count` generated creates over no cwd, an empty one,
/// a missing path (1), a file (2) and a dir (3).
fn cwd_scenario(rng: &mut Rng, base: &Path, count: u64) -> Scenario {
    let paths = [
        base.join("cwd-missing"),
        base.join("cwd-file"),
        base.join("cwd-dir"),
    ];
    std::fs::write(&paths[1], "a file").unwrap();
    std::fs::create_dir(&paths[2]).unwrap();
    let index = |path: &Path| {
        paths
            .iter()
            .position(|known| known == path)
            .map_or_else(|| path.display().to_string(), |at| (at + 1).to_string())
    };
    let (mut events, mut transcript) = (String::new(), String::new());
    for _ in 0..count {
        let pick = rng.below(5);
        let named = match pick {
            0 => None,
            1 => Some(String::new()),
            at => Some(
                paths[usize::try_from(at - 2).unwrap()]
                    .display()
                    .to_string(),
            ),
        };
        match pick {
            0 | 1 => events.push_str("w n\n"),
            2 => events.push_str("w g 1\n"),
            3 => events.push_str("w f 2\n"),
            _ => events.push_str("w d 3\n"),
        }
        match session_cwd(named.as_deref()) {
            Ok(path) => writeln!(transcript, "ok {}", index(&path)).unwrap(),
            Err(CwdError::Missing) => transcript.push_str("missing\n"),
            Err(CwdError::Gone(path)) => writeln!(transcript, "gone {}", index(&path)).unwrap(),
            Err(CwdError::NotADirectory(path)) => {
                writeln!(transcript, "notdir {}", index(&path)).unwrap();
            }
        }
    }
    Scenario {
        name: "cwds".to_string(),
        events,
        transcript,
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn the_local_access_code_equals_the_bend_model() {
    let mut rng = Rng(0x0f5_0de5);
    let home = tempfile::tempdir().unwrap();
    let mut scenarios = Vec::new();

    let sockets = home.path().join("sockets");
    std::fs::create_dir(&sockets).unwrap();
    scenarios.push(socket_scenario(&mut rng, &sockets, 48));
    scenarios.push(peer_scenario(&mut rng));
    scenarios.push(cwd_scenario(&mut rng, home.path(), 48));

    // The daemon's start dirs and the socket dir.
    let agent = home.path().join("agent");
    crate::paths::ensure_dir(&agent.join("sessions")).unwrap();
    prepare_socket_dir(&home.path().join("run").join("eukhe-sockets")).unwrap();
    scenarios.push(creation_scenario("daemon dirs", &agent));
    scenarios.push(creation_scenario("socket dir", &home.path().join("run")));

    // The auth store on a fresh agent dir.
    let auth_agent = home.path().join("auth-agent");
    eukhe_core::auth::AuthStorage::create(&auth_agent)
        .set(
            "faux",
            eukhe_core::auth::AuthCredential::ApiKey {
                key: "sk-bridge".to_string(),
                prime_team: None,
            },
        )
        .expect("the auth store writes");
    scenarios.push(creation_scenario("auth store", &auth_agent));

    // A worker's session, then a legacy import and a fork into a fresh
    // sessions root.
    let (worker_dir, _worker) =
        crate::durable_test_support::created_worker("fsmode-bridge", serde_json::json!([])).await;
    scenarios.push(creation_scenario(
        "worker session",
        &worker_dir.path().join("agent"),
    ));
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
    scenarios.push(creation_scenario("import and fork", &store));

    compare("bridge/bridge_fsmode.bend", scenarios);
}
