//! `ssh://` reads against a fake `ssh`: a script that records its
//! arguments and plays a host by name. The host `box` runs the remote
//! command through `sh -c` in a temporary home, as a real remote shell
//! does, so a path that holds shell syntax shows that the quoting keeps
//! it one word.

use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

use eukhe_docs::Url;

use super::*;

/// A fake `ssh` under `dir`: it writes its arguments, NUL-separated, to
/// `dir/args`, and plays the host after `--`.
fn fake_ssh(dir: &Path) -> PathBuf {
    let script = dir.join("ssh");
    std::fs::create_dir_all(dir.join("home")).unwrap();
    std::fs::write(
        &script,
        format!(
            r#"#!/bin/sh
dir='{dir}'
printf '%s\0' "$@" > "$dir/args"
while [ "$1" != "--" ]; do shift; done
host=$2
command=$3
case "$host" in
  box) cd "$dir/home" && exec sh -c "$command" ;;
  locked) echo "cat: secret: Permission denied" >&2; exit 1 ;;
  nokey) echo "Warning: Permanently added 'nokey' (ED25519) to the list of known hosts." >&2
         echo "me@nokey: Permission denied (publickey,password)." >&2; exit 255 ;;
  newkey) echo "Host key verification failed." >&2; exit 255 ;;
  nowhere) echo "ssh: Could not resolve hostname nowhere: Name or service not known" >&2; exit 255 ;;
  refused) echo "ssh: connect to host refused port 22: Connection refused" >&2; exit 255 ;;
  slow) exec sleep 30 ;;
  flood) exec yes ;;
esac
echo "unknown fake host $host" >&2
exit 255
"#,
            dir = dir.display()
        ),
    )
    .unwrap();
    std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
    script
}

const HOSTS: &[&str] = &[
    "box", "locked", "nokey", "newkey", "nowhere", "refused", "slow", "flood",
];

fn hosts() -> Vec<String> {
    HOSTS.iter().map(|host| (*host).to_owned()).collect()
}

/// Read `url` through `program` with a 5 s budget and `cap`.
async fn read(program: &Path, url: &str, cap: Option<usize>) -> Result<String, SshError> {
    read_within(program, url, cap, Duration::from_secs(5)).await
}

async fn read_within(
    program: &Path,
    url: &str,
    cap: Option<usize>,
    budget: Duration,
) -> Result<String, SshError> {
    let parsed = Url::parse(url).expect("a URL").expect("a served scheme");
    let remote = parsed.remote().expect("a remote path");
    SshRead::new(program.as_os_str(), url, remote, &hosts(), budget, cap)?
        .run()
        .await
}

fn recorded(dir: &Path) -> Vec<String> {
    std::fs::read(dir.join("args"))
        .unwrap()
        .split(|byte| *byte == 0)
        .filter(|arg| !arg.is_empty())
        .map(|arg| String::from_utf8(arg.to_vec()).unwrap())
        .collect()
}

#[test]
fn the_arguments_keep_the_host_after_dashdash_and_the_path_one_quoted_word() {
    let arguments = |path: &str, budget_ms: u64| {
        SshRead {
            program: OsStr::new("ssh"),
            url: "ssh://box/x",
            remote: Remote {
                host: "me@box",
                path: path.to_owned(),
            },
            budget: Duration::from_millis(budget_ms),
            cap: None,
        }
        .arguments()
    };
    let expected = |timeout: &str, command: &str| {
        [
            "-T",
            "-o",
            "BatchMode=yes",
            "-o",
            timeout,
            "-o",
            "ClearAllForwardings=yes",
            "--",
            "me@box",
            command,
        ]
        .map(str::to_owned)
        .to_vec()
    };
    assert_eq!(
        [
            arguments("/etc/hosts", 30_000),
            arguments("notes/it's.md", 1),
            arguments("/a'; rm -rf ~; echo '", 1_500),
            arguments("$(touch pwned) `id` \"x\"\n;", 0),
        ],
        [
            expected("ConnectTimeout=30", "cat -- '/etc/hosts'"),
            expected("ConnectTimeout=1", r"cat -- 'notes/it'\''s.md'"),
            expected("ConnectTimeout=2", r"cat -- '/a'\''; rm -rf ~; echo '\'''"),
            expected("ConnectTimeout=1", "cat -- '$(touch pwned) `id` \"x\"\n;'"),
        ]
    );
}

#[test]
fn a_host_outside_ssh_hosts_is_rejected_by_name() {
    let remote = || Remote {
        host: "box",
        path: "/etc/hosts".to_owned(),
    };
    let new = |hosts: &[String]| {
        SshRead::new(
            OsStr::new("ssh"),
            "ssh://box/etc/hosts",
            remote(),
            hosts,
            Duration::from_secs(1),
            None,
        )
        .map(|read| read.remote)
    };
    let refused = |allowed: &str| {
        Err(SshError::NotAllowed {
            url: "ssh://box/etc/hosts".to_owned(),
            host: "box".to_owned(),
            allowed: allowed.to_owned(),
        })
    };
    let results = [
        new(&[]),
        new(&["other".to_owned(), "me@box".to_owned()]),
        new(&["box".to_owned()]),
    ];
    assert_eq!(
        results,
        [
            refused("it is empty, so every ssh:// read is rejected"),
            refused("it allows other, me@box"),
            Ok(remote()),
        ]
    );
    assert_eq!(
        results[0].clone().map(|_| ()).unwrap_err().to_string(),
        "ssh://box/etc/hosts: the host box is not in the setting `ssh.hosts` (it is empty, so every ssh:// read is rejected); add the host to `ssh.hosts` in the global settings.json to read from it"
    );
}

#[tokio::test]
async fn a_path_with_shell_syntax_reads_the_file_of_that_name_and_runs_nothing() {
    let dir = tempfile::tempdir().unwrap();
    let ssh = fake_ssh(dir.path());
    let name = "it's $(touch pwned) `touch pwned2` ; touch pwned3 #\n.txt";
    std::fs::write(dir.path().join("home").join(name), "the text\n").unwrap();
    std::fs::write(dir.path().join("abs.txt"), "absolute\n").unwrap();
    let home_url = format!("ssh://box/~/{name}");
    let abs_url = format!("ssh://box{}/abs.txt", dir.path().display());
    assert_eq!(
        [
            read(&ssh, &home_url, None).await,
            read(&ssh, &abs_url, None).await,
        ],
        [Ok("the text\n".to_owned()), Ok("absolute\n".to_owned())]
    );
    assert_eq!(
        recorded(dir.path()),
        [
            "-T",
            "-o",
            "BatchMode=yes",
            "-o",
            "ConnectTimeout=5",
            "-o",
            "ClearAllForwardings=yes",
            "--",
            "box",
            &format!("cat -- '{}/abs.txt'", dir.path().display()),
        ]
    );
    let home = dir.path().join("home");
    assert_eq!(
        ["pwned", "pwned2", "pwned3"].map(|file| home.join(file).exists()),
        [false; 3]
    );
}

#[tokio::test]
async fn ssh_and_remote_failures_are_typed() {
    let dir = tempfile::tempdir().unwrap();
    let ssh = fake_ssh(dir.path());
    std::fs::write(dir.path().join("home/bin"), b"a\0b").unwrap();
    std::fs::write(dir.path().join("home/latin1"), b"caf\xe9").unwrap();
    let url = |rest: &str| format!("ssh://{rest}");
    let mut results = Vec::new();
    for rest in [
        "box/~/missing",
        "box/~/bin/x",
        "box/~",
        "locked/~/secret",
        "nokey/x",
        "newkey/x",
        "nowhere/x",
        "refused/x",
        "box/~/bin",
        "box/~/latin1",
    ] {
        results.push(read(&ssh, &url(rest), None).await);
    }
    results.push(read(&dir.path().join("no-ssh"), &url("box/x"), None).await);
    let detail = |text: &str| text.to_owned();
    assert_eq!(
        results,
        [
            Err(SshError::NotFound {
                url: url("box/~/missing"),
                detail: detail("cat: missing: No such file or directory"),
            }),
            Err(SshError::NotFound {
                url: url("box/~/bin/x"),
                detail: detail("cat: bin/x: Not a directory"),
            }),
            Err(SshError::IsDirectory { url: url("box/~") }),
            Err(SshError::PermissionDenied {
                url: url("locked/~/secret"),
                detail: detail("cat: secret: Permission denied"),
            }),
            Err(SshError::Auth {
                url: url("nokey/x"),
                detail: detail("me@nokey: Permission denied (publickey,password)."),
            }),
            Err(SshError::HostKey {
                url: url("newkey/x"),
                detail: detail("Host key verification failed."),
            }),
            Err(SshError::UnknownHost {
                url: url("nowhere/x"),
                detail: detail(
                    "ssh: Could not resolve hostname nowhere: Name or service not known"
                ),
            }),
            Err(SshError::Unreachable {
                url: url("refused/x"),
                detail: detail("ssh: connect to host refused port 22: Connection refused"),
            }),
            Err(SshError::Binary {
                url: url("box/~/bin"),
                bytes: 3,
            }),
            Err(SshError::Binary {
                url: url("box/~/latin1"),
                bytes: 4,
            }),
            Err(SshError::NoSsh { url: url("box/x") }),
        ]
    );
    assert_eq!(
        results
            .iter()
            .map(|result| result.as_ref().unwrap_err().reason())
            .collect::<Vec<_>>(),
        [
            "not_found",
            "not_found",
            "is_directory",
            "permission_denied",
            "auth",
            "host",
            "host",
            "host",
            "binary",
            "binary",
            "io",
        ]
    );
}

#[tokio::test]
async fn the_output_cap_keeps_the_first_bytes_and_counts_the_rest() {
    let dir = tempfile::tempdir().unwrap();
    let ssh = fake_ssh(dir.path());
    std::fs::write(dir.path().join("home/big"), "0123456789".repeat(10)).unwrap();
    std::fs::write(dir.path().join("home/accents"), "ééééé").unwrap();
    std::fs::write(dir.path().join("home/fits"), "0123456789").unwrap();
    assert_eq!(
        [
            read(&ssh, "ssh://box/~/big", Some(25)).await,
            read(&ssh, "ssh://box/~/accents", Some(5)).await,
            read(&ssh, "ssh://box/~/fits", Some(10)).await,
            read(&ssh, "ssh://box/~/big", None).await,
        ],
        [
            Ok(
                "[ssh://box/~/big: 25 of 100 bytes shown; the output cap dropped 75]\n0123456789012345678901234"
                    .to_owned()
            ),
            Ok("[ssh://box/~/accents: 4 of 10 bytes shown; the output cap dropped 6]\néé".to_owned()),
            Ok("0123456789".to_owned()),
            Ok("0123456789".repeat(10)),
        ]
    );
}

#[tokio::test]
async fn the_blocking_budget_ends_the_read_and_kills_ssh() {
    let dir = tempfile::tempdir().unwrap();
    let ssh = fake_ssh(dir.path());
    let budget = Duration::from_millis(300);
    let started = std::time::Instant::now();
    let slow = read_within(&ssh, "ssh://slow/x", Some(10), budget).await;
    let flood = read_within(&ssh, "ssh://flood/x", Some(10), budget).await;
    let elapsed = started.elapsed();
    assert_eq!(
        slow,
        Err(SshError::Timeout {
            url: "ssh://slow/x".to_owned(),
            budget_ms: 300,
            bytes: 0,
        })
    );
    let flood = flood.unwrap();
    let (notice, text) = flood.split_once('\n').unwrap();
    let dropped: u64 = notice
        .strip_prefix("[ssh://flood/x: the first 10 bytes shown; the output cap dropped ")
        .and_then(|rest| rest.strip_suffix(" or more (the read stopped at the blocking budget)]"))
        .unwrap()
        .parse()
        .unwrap();
    assert_eq!((text, dropped > 0), ("y\ny\ny\ny\ny\n", true));
    assert!(elapsed < Duration::from_secs(10), "{elapsed:?}");
}
