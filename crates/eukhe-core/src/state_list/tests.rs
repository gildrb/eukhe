use super::*;

fn parts(kinds: &[(StateKind, &str)]) -> Vec<StatePart> {
    kinds
        .iter()
        .map(|(kind, path)| StatePart {
            kind: *kind,
            path: PathBuf::from(path),
        })
        .collect()
}

#[cfg(target_os = "macos")]
fn auto_start(_config: &str) -> Vec<StatePart> {
    parts(&[(StateKind::AutoStart, "/home/u/Library/LaunchAgents")])
}

#[cfg(not(target_os = "macos"))]
fn auto_start(config: &str) -> Vec<StatePart> {
    parts(&[
        (StateKind::AutoStart, &format!("{config}/systemd/user")),
        (StateKind::AutoStart, &format!("{config}/autostart")),
    ])
}

/// Every part of an install with no override in the environment.
#[test]
fn the_list_names_every_part_of_a_default_install() {
    let list = state_list(&Install {
        agent_dir: Path::new("/home/u/.eukhe"),
        home: Some(Path::new("/home/u")),
        executable: Some(Path::new("/opt/eukhe/bin/eukhe-daemon")),
        cwd: Path::new("/work"),
        env: &|_| None,
    });
    let mut expected = parts(&[
        (StateKind::AgentDir, "/home/u/.eukhe"),
        (StateKind::RunDir, "/home/u/.eukhe/run"),
        (StateKind::Credentials, "/home/u/.eukhe/auth.json"),
        (StateKind::Credentials, "/home/u/.eukhe/dashboard-token"),
        (StateKind::Credentials, "/home/u/.aws"),
        (StateKind::WorkRoot, "/home/u/.eukhe-work"),
        (StateKind::Executables, "/opt/eukhe/bin"),
    ]);
    expected.extend(auto_start("/home/u/.config"));
    assert_eq!(list, expected);
}

/// An agent dir override moves the run dir, credentials and work root
/// with it; the AWS file variables add their files (a relative one
/// against the working directory); `XDG_CONFIG_HOME` moves the Linux
/// auto-start dirs. Without a home or executable, those parts drop out.
#[test]
fn overrides_move_their_parts() {
    let env = |name: &str| match name {
        "AWS_SHARED_CREDENTIALS_FILE" => Some(OsString::from("/keys/aws")),
        "AWS_CONFIG_FILE" => Some(OsString::from("aws.cfg")),
        "XDG_CONFIG_HOME" => Some(OsString::from("/xdg")),
        _ => None,
    };
    let list = state_list(&Install {
        agent_dir: Path::new("/state/agent"),
        home: None,
        executable: None,
        cwd: Path::new("/work"),
        env: &env,
    });
    let mut expected = parts(&[
        (StateKind::AgentDir, "/state/agent"),
        (StateKind::RunDir, "/state/agent/run"),
        (StateKind::Credentials, "/state/agent/auth.json"),
        (StateKind::Credentials, "/state/agent/dashboard-token"),
        (StateKind::Credentials, "/keys/aws"),
        (StateKind::Credentials, "/work/aws.cfg"),
        (StateKind::WorkRoot, "/state/agent-work"),
    ]);
    if cfg!(not(target_os = "macos")) {
        expected.extend(auto_start("/xdg"));
    }
    assert_eq!(list, expected);
}
