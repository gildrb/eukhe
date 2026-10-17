use std::path::{Path, PathBuf};

use serde_json::json;

use super::{
    KernelTransport, KernelTransportError, KernelWrapper, PathMap, PathMapError, PathMount,
    WrappedLaunch, WrapperCommand,
};

fn map() -> PathMap {
    PathMap::new(vec![
        PathMount {
            sandbox: PathBuf::from("/work"),
            host: PathBuf::from("/home/u/project"),
        },
        PathMount {
            sandbox: PathBuf::from("/work/data"),
            host: PathBuf::from("/srv/data"),
        },
    ])
}

#[test]
fn paths_map_through_the_deepest_mount_both_ways() {
    let map = map();
    assert_eq!(
        (
            map.to_host(Path::new("/work/src/a.rs")),
            map.to_host(Path::new("/work/data/x.csv")),
            map.to_host(Path::new("/work/src/../../etc/passwd")),
            map.to_host(Path::new("/etc/passwd")),
            map.to_sandbox(Path::new("/srv/data/x.csv")),
            map.to_sandbox(Path::new("/home/u/project")),
        ),
        (
            Ok(PathBuf::from("/home/u/project/src/a.rs")),
            Ok(PathBuf::from("/srv/data/x.csv")),
            Err(PathMapError::Outside(PathBuf::from(
                "/work/src/../../etc/passwd"
            ))),
            Err(PathMapError::Outside(PathBuf::from("/etc/passwd"))),
            Ok(PathBuf::from("/work/data/x.csv")),
            Ok(PathBuf::from("/work")),
        )
    );
}

#[test]
fn fs_requests_map_cwd_and_paths_and_reject_outside_ones() {
    let map = map();
    let request = |request_type: &str, args: serde_json::Value| {
        let mut data = json!({ "type": request_type, "cwd": "/work/src", "args": args })
            .as_object()
            .cloned()
            .expect("object");
        map.fs_request_to_host(request_type, &mut data)
            .map(|()| serde_json::Value::Object(data))
    };
    assert_eq!(
        request("fs.read", json!({ "path": "a.rs:2-3" })),
        Ok(
            json!({ "type": "fs.read", "cwd": "/home/u/project/src", "args": { "path": "a.rs:2-3" } })
        )
    );
    assert_eq!(
        request("fs.read", json!({ "file_path": "/work/b.rs" })),
        Ok(
            json!({ "type": "fs.read", "cwd": "/home/u/project/src", "args": { "file_path": "/home/u/project/b.rs" } })
        )
    );
    // Relative into another mount: the host gets the absolute host path.
    assert_eq!(
        request("fs.grep", json!({ "pattern": "x", "path": "../data;lib" })),
        Ok(
            json!({ "type": "fs.grep", "cwd": "/home/u/project/src", "args": { "pattern": "x", "path": "/srv/data;lib" } })
        )
    );
    assert_eq!(
        request(
            "fs.edit",
            json!({ "input": "[/work/a.rs#1A2B]\nPUT 1.=1:\n+[keep]\n[b.rs]\nMV /work/c.rs\n" })
        ),
        Ok(
            json!({ "type": "fs.edit", "cwd": "/home/u/project/src", "args": {
            "input": "[/home/u/project/a.rs#1A2B]\nPUT 1.=1:\n+[keep]\n[b.rs]\nMV /home/u/project/c.rs\n"
        } })
        )
    );
    assert_eq!(
        (
            request("fs.read", json!({ "path": "../../etc/passwd" })),
            request("fs.write", json!({ "path": "/etc/passwd", "content": "x" })),
            request("fs.read", json!({ "path": "~/.ssh/id_ed25519" })),
            request("fs.edit", json!({ "input": "[/etc/hosts#1A2B]\nREM" })),
        ),
        (
            Err(PathMapError::Outside(PathBuf::from(
                "/work/src/../../etc/passwd"
            ))),
            Err(PathMapError::Outside(PathBuf::from("/etc/passwd"))),
            Err(PathMapError::Home("~/.ssh/id_ed25519".to_owned())),
            Err(PathMapError::Outside(PathBuf::from("/etc/hosts"))),
        )
    );
    let mut outside_cwd = json!({ "type": "fs.read", "cwd": "/tmp", "args": { "path": "a" } })
        .as_object()
        .cloned()
        .expect("object");
    assert_eq!(
        map.fs_request_to_host("fs.read", &mut outside_cwd),
        Err(PathMapError::Outside(PathBuf::from("/tmp")))
    );
}

#[test]
fn fs_requests_reject_a_symlink_in_a_mount_that_points_out_of_every_mount() {
    let root = tempfile::tempdir().expect("tempdir");
    let project = root.path().join("project");
    let outside = root.path().join("outside");
    std::fs::create_dir_all(project.join("src")).expect("src");
    std::fs::create_dir_all(outside.join("sub")).expect("outside");
    std::fs::write(outside.join("secret"), "s").expect("secret");
    std::os::unix::fs::symlink(&outside, project.join("x")).expect("x");
    std::os::unix::fs::symlink(outside.join("sub"), project.join("deep")).expect("deep");
    std::os::unix::fs::symlink(project.join("src"), project.join("inner")).expect("inner");
    // The mount's host path is itself a symlink: both sides resolve.
    let mount_host = root.path().join("project-link");
    std::os::unix::fs::symlink(&project, &mount_host).expect("mount link");
    let map = PathMap::new(vec![PathMount {
        sandbox: PathBuf::from("/work"),
        host: mount_host.clone(),
    }]);
    let request = |cwd: &str, request_type: &str, args: serde_json::Value| {
        let mut data = json!({ "type": request_type, "cwd": cwd, "args": args })
            .as_object()
            .cloned()
            .expect("object");
        map.fs_request_to_host(request_type, &mut data)
            .map(|()| serde_json::Value::Object(data))
    };
    let host_cwd = mount_host.to_string_lossy().into_owned();
    assert_eq!(
        (
            request("/work", "fs.read", json!({ "path": "/work/x/secret" })),
            request("/work", "fs.read", json!({ "path": "x/secret" })),
            request(
                "/work",
                "fs.write",
                json!({ "path": "x/new.txt", "content": "n" })
            ),
            request("/work", "fs.read", json!({ "path": "deep/../secret" })),
            request("/work/x", "fs.read", json!({ "path": "secret" })),
            request(
                "/work",
                "fs.edit",
                json!({ "input": "[x/secret#1A2B]\nREM" })
            ),
            request("/work", "fs.read", json!({ "path": "inner/a.rs" })),
            request(
                "/work",
                "fs.write",
                json!({ "path": "/work/src/new/b.rs", "content": "b" })
            ),
        ),
        (
            Err(PathMapError::Outside(PathBuf::from("/work/x/secret"))),
            Err(PathMapError::Outside(PathBuf::from("/work/x/secret"))),
            Err(PathMapError::Outside(PathBuf::from("/work/x/new.txt"))),
            Err(PathMapError::Outside(PathBuf::from("/work/deep/../secret"))),
            Err(PathMapError::Outside(PathBuf::from("/work/x"))),
            Err(PathMapError::Outside(PathBuf::from("/work/x/secret"))),
            Ok(json!({ "type": "fs.read", "cwd": host_cwd, "args": { "path": "inner/a.rs" } })),
            Ok(json!({ "type": "fs.write", "cwd": host_cwd, "args": {
                "path": mount_host.join("src/new/b.rs").to_string_lossy(),
                "content": "b",
            } })),
        )
    );
}

#[test]
fn fs_replies_map_host_paths_back_to_the_sandbox() {
    let mut reply = json!({
        "path": "a.rs",
        "absolute": "/home/u/project/src/a.rs",
        "files": [{ "absolute": "/srv/data/x.csv", "destination": "/elsewhere/y" }],
    });
    map().fs_reply_to_sandbox(&mut reply);
    assert_eq!(
        reply,
        json!({
            "path": "a.rs",
            "absolute": "/work/src/a.rs",
            "files": [{ "absolute": "/work/data/x.csv", "destination": "/elsewhere/y" }],
        })
    );
}

#[test]
fn the_setting_names_the_transport() {
    assert_eq!(
        KernelTransport::from_setting(None).expect("local"),
        KernelTransport::Local
    );
    assert_eq!(
        KernelTransport::from_setting(Some(&json!({
            "argvPrefix": ["ssh", "-T", "box"],
            "command": "shell",
            "pathMap": [{ "sandbox": "/w/./x", "host": "/h" }],
            "env": ["LANG"],
        })))
        .expect("wrapped"),
        KernelTransport::Wrapped(KernelWrapper {
            argv_prefix: vec!["ssh".into(), "-T".into(), "box".into()],
            command: WrapperCommand::Shell,
            python: "python3".into(),
            path_map: PathMap::new(vec![PathMount {
                sandbox: PathBuf::from("/w/x"),
                host: PathBuf::from("/h"),
            }]),
            env: vec!["LANG".into()],
        })
    );
    let refused = |value: serde_json::Value| {
        KernelTransport::from_setting(Some(&value))
            .expect_err("refused")
            .to_string()
    };
    assert_eq!(
        [
            refused(json!({ "argvPrefix": [] })),
            refused(json!({ "argvPrefix": ["sh"], "pathMap": [{ "sandbox": "w", "host": "/h" }] })),
            refused(json!({ "argvPrefix": ["sh"], "env": ["A=B"] })),
        ],
        [
            KernelTransportError::EmptyPrefix.to_string(),
            KernelTransportError::RelativeMount(PathBuf::from("w")).to_string(),
            KernelTransportError::BadEnvName("A=B".into()).to_string(),
        ]
    );
}

#[test]
fn a_wrapped_launch_runs_the_kernel_in_the_mapped_cwd_with_the_allowed_env_only() {
    let wrapper = KernelWrapper {
        argv_prefix: vec!["docker".into(), "exec".into(), "-i".into(), "box".into()],
        command: WrapperCommand::Argv,
        python: "/opt/py/bin/python".into(),
        path_map: map(),
        env: vec!["LANG".into(), "UNSET_HERE".into()],
    };
    let kernel_env = vec![
        ("EUKHE_BASH_SHELL".to_owned(), "/run/bin/bash".to_owned()),
        ("EUKHE_CHAT_MEMORY".to_owned(), "1".to_owned()),
        (
            "EUKHE_CODING_AGENT_DIR".to_owned(),
            "/home/u/project/.eukhe".to_owned(),
        ),
    ];
    let host_env = |name: &str| (name == "LANG").then(|| "C.UTF-8".to_owned());
    let launch = wrapper
        .launch(
            Path::new("/home/u/project/src"),
            &kernel_env,
            host_env,
            &[
                PathBuf::from("/home/u/project/skill"),
                PathBuf::from("/nowhere"),
            ],
        )
        .expect("launch");
    let script = "cd /work/src && exec env EUKHE_CHAT_MEMORY=1 \
        EUKHE_CODING_AGENT_DIR=/work/.eukhe LANG=C.UTF-8 EUKHE_KERNEL_OWNER=stdin \
        PYTHONPATH=/work/skill\"${PYTHONPATH:+:$PYTHONPATH}\" /opt/py/bin/python -P -m rlm.repl";
    assert_eq!(
        launch,
        WrappedLaunch {
            argv: ["docker", "exec", "-i", "box", "sh", "-c", script]
                .map(str::to_owned)
                .to_vec(),
            unmapped_env: vec!["EUKHE_BASH_SHELL".to_owned()],
        }
    );
    let ssh = KernelWrapper {
        argv_prefix: vec!["ssh".into(), "-T".into(), "box".into()],
        command: WrapperCommand::Shell,
        env: Vec::new(),
        ..wrapper
    };
    assert_eq!(
        ssh.launch(Path::new("/home/u/project/my dir"), &[], host_env, &[])
            .expect("launch")
            .argv,
        [
            "ssh",
            "-T",
            "box",
            "cd '/work/my dir' && exec env EUKHE_KERNEL_OWNER=stdin /opt/py/bin/python -P -m rlm.repl",
        ]
        .map(str::to_owned)
        .to_vec()
    );
    assert_eq!(
        ssh.launch(Path::new("/tmp"), &[], host_env, &[]),
        Err(PathMapError::Outside(PathBuf::from("/tmp")))
    );
}
