use serde_json::json;

use super::*;
use crate::resources::LoadedResources;
use crate::skills::{create_synthetic_source_info, Skill, SkillKind, SourceScope};

/// The documents of a session whose workspace (`repo://`) is `dir/ws` and
/// whose one skill `notes` lives in `dir/skills/notes`.
fn registry(dir: &std::path::Path) -> HostRequestRegistry {
    let registry = HostRequestRegistry::default();
    let skill_dir = dir.join("skills/notes");
    let host = DocumentsHost {
        documents: eukhe_docs::Documents::new(dir.join("locks"), None),
        workspace: dir.join("ws"),
        resources: Arc::new(LoadedResources {
            skills: vec![Skill {
                name: "notes".to_owned(),
                description: "Notes".to_owned(),
                file_path: skill_dir.join("SKILL.md"),
                base_dir: skill_dir.clone(),
                source_info: create_synthetic_source_info(
                    &skill_dir.to_string_lossy(),
                    "user",
                    SourceScope::User,
                    None,
                ),
                disable_model_invocation: false,
                kind: SkillKind::Markdown,
                python: None,
            }],
            ..LoadedResources::default()
        }),
        memory: None,
        deps: std::sync::Weak::new(),
    };
    register(&registry, &Arc::new(host));
    registry
}

async fn call(
    registry: &HostRequestRegistry,
    request_type: &str,
    cwd: &Path,
    args: Value,
) -> Value {
    let handler = registry.get(request_type).unwrap();
    handler(HostCall {
        data: json!({"type": request_type, "cwd": cwd, "args": args}),
        cell_source_code: None,
        call: None,
    })
    .await
    .unwrap()
}

#[tokio::test]
async fn write_then_read_share_one_store() {
    let dir = tempfile::tempdir().unwrap();
    let registry = registry(dir.path());
    let tag = eukhe_docs::file_hash("a\nb\n");
    let written = call(
        &registry,
        "fs.write",
        dir.path(),
        json!({"path": "x.txt", "content": "a\nb\n"}),
    )
    .await;
    assert_eq!(
        written,
        json!({
            "outcome": "done",
            "version": "write@1",
            "path": "x.txt",
            "absolute": dir.path().join("x.txt"),
            "created": true,
            "bytes": 4,
            "tag": tag,
            "made_executable": false,
            "rendered": format!("[x.txt#{tag}]\nSuccessfully wrote 4 bytes to x.txt"),
            "warnings": [],
        })
    );
    let read = call(
        &registry,
        "fs.read",
        dir.path(),
        json!({"path": "x.txt:2-2"}),
    )
    .await;
    assert_eq!(
        read,
        json!({
            "outcome": "done",
            "version": "read@1",
            "path": "x.txt",
            "absolute": dir.path().join("x.txt"),
            "rendered": format!("[x.txt#{tag}]\n1:a\n2:b"),
            "diags": [],
            "kind": "file",
            "tag": tag,
            "text": "a\nb\n",
            "total_lines": 2,
            "shown": [[1, 2]],
            "warnings": [],
        })
    );
}

#[tokio::test]
async fn read_rejection_carries_reason_and_message() {
    let dir = tempfile::tempdir().unwrap();
    let registry = registry(dir.path());
    let reply = call(&registry, "fs.read", dir.path(), json!({"path": "nope.rs"})).await;
    assert_eq!(
        reply,
        json!({
            "outcome": "rejected",
            "version": "read@1",
            "reason": "not_found",
            "message": "Path 'nope.rs' not found",
        })
    );
}

#[tokio::test]
async fn kernel_arguments_repair_by_the_wire_contract() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("a.rs"), "fn one() {}\n").unwrap();
    let registry = registry(dir.path());
    let repaired = call(
        &registry,
        "fs.grep",
        dir.path(),
        json!({"regex": "ONE", "file_path": "a.rs", "case": "false"}),
    )
    .await;
    assert_eq!(
        (
            &repaired["outcome"],
            &repaired["files"][0]["matches"],
            &repaired["warnings"]
        ),
        (
            &json!("done"),
            &json!([[1, "fn one() {}"]]),
            &json!([
                "Repaired argument: regex read as pattern",
                "Repaired argument: file_path read as path",
                "Repaired argument: case=\"false\" read as false",
            ])
        )
    );
    let unknown = call(
        &registry,
        "fs.read",
        dir.path(),
        json!({"path": "a.rs", "offset": 3}),
    )
    .await;
    assert_eq!(
        unknown,
        json!({
            "outcome": "rejected",
            "version": "read@1",
            "reason": "arguments",
            "message": "read has no argument `offset`. Valid arguments: i, path.",
        })
    );
    let refused = call(
        &registry,
        "fs.edit",
        dir.path(),
        json!({"old_string": "one", "new_string": "two"}),
    )
    .await;
    assert_eq!(
        (&refused["reason"], &refused["message"]),
        (
            &json!("arguments"),
            &json!("edit does not take `old_string`: edit takes a hashline patch, not old/new strings. read or grep the file, then send '[path#TAG]\\nPUT 12.=14:\\n+new line' with the header and line numbers they printed.")
        )
    );
}

#[tokio::test]
async fn edit_grep_and_glob_share_the_read_anchors() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("a.rs"), "fn one() {}\nfn two() {}\n").unwrap();
    let registry = registry(dir.path());
    let grep = call(
        &registry,
        "fs.grep",
        dir.path(),
        json!({"pattern": "two", "path": "a.rs"}),
    )
    .await;
    let tag = eukhe_docs::file_hash("fn one() {}\nfn two() {}\n");
    assert_eq!(
        (
            &grep["version"],
            &grep["files"][0]["matches"],
            &grep["files"][0]["tag"]
        ),
        (&json!("grep@1"), &json!([[2, "fn two() {}"]]), &json!(tag))
    );
    let edited = call(
        &registry,
        "fs.edit",
        dir.path(),
        json!({"input": format!("[a.rs#{tag}]\nPUT 2.=2:\n+fn three() {{}}")}),
    )
    .await;
    assert_eq!(
        (
            &edited["outcome"],
            &edited["version"],
            &edited["files"][0]["change"]
        ),
        (&json!("done"), &json!("edit@hl.1"), &json!("updated"))
    );
    assert_eq!(
        std::fs::read_to_string(dir.path().join("a.rs")).unwrap(),
        "fn one() {}\nfn three() {}\n"
    );
    let globbed = call(&registry, "fs.glob", dir.path(), json!({"path": "*.rs"})).await;
    assert_eq!(
        (&globbed["version"], &globbed["paths"]),
        (&json!("glob@1"), &json!(["a.rs"]))
    );
}

#[tokio::test]
async fn file_urls_read_under_their_root() {
    let dir = tempfile::tempdir().unwrap();
    let registry = registry(dir.path());
    std::fs::create_dir_all(dir.path().join("ws/src")).unwrap();
    std::fs::create_dir_all(dir.path().join("skills/notes/refs")).unwrap();
    std::fs::write(dir.path().join("ws/src/a.rs"), "fn a() {}\n").unwrap();
    std::fs::write(dir.path().join("skills/notes/SKILL.md"), "# Notes\n").unwrap();
    std::fs::write(dir.path().join("skills/notes/refs/r.md"), "ref\n").unwrap();
    let mut rendered = Vec::new();
    for path in [
        "repo://src/a.rs",
        "skill://notes",
        "skill://notes/refs/../refs/r.md",
    ] {
        let reply = call(&registry, "fs.read", dir.path(), json!({ "path": path })).await;
        rendered.push((reply["absolute"].clone(), reply["rendered"].clone()));
    }
    let tag = eukhe_docs::file_hash;
    assert_eq!(
        rendered,
        [
            (
                json!(dir.path().join("ws/src/a.rs")),
                json!(format!(
                    "[ws/src/a.rs#{}]\n1:fn a() {{}}",
                    tag("fn a() {}\n")
                ))
            ),
            (
                json!(dir.path().join("skills/notes/SKILL.md")),
                json!(format!(
                    "[skills/notes/SKILL.md#{}]\n1:# Notes",
                    tag("# Notes\n")
                ))
            ),
            (
                json!(dir.path().join("skills/notes/refs/r.md")),
                json!(format!("[skills/notes/refs/r.md#{}]\n1:ref", tag("ref\n")))
            ),
        ]
    );
}

#[tokio::test]
async fn urls_the_session_cannot_serve_are_typed_rejections() {
    let dir = tempfile::tempdir().unwrap();
    let registry = registry(dir.path());
    std::fs::create_dir_all(dir.path().join("ws")).unwrap();
    std::fs::write(dir.path().join("x"), "outside\n").unwrap();
    std::os::unix::fs::symlink(dir.path().join("x"), dir.path().join("ws/leak")).unwrap();
    let mut replies = Vec::new();
    for path in [
        "repo://../x",
        "repo://leak",
        "skill://notes/../../x",
        "ssh://host/etc/passwd",
        "ssh://-oProxyCommand=x/etc/passwd",
        "ssh://host/~/../etc/passwd",
        "sftp://host/etc/passwd",
        "skill://nope/SKILL.md",
        "memory://",
        "agent://Scout",
        "agent://a/b",
        "mcp://notes/file:///a.txt",
    ] {
        replies.push(call(&registry, "fs.read", dir.path(), json!({ "path": path })).await);
    }
    let rejected = |reason: &str, message: &str| {
        json!({
            "outcome": "rejected",
            "version": "read@1",
            "reason": reason,
            "message": message,
        })
    };
    assert_eq!(
        replies,
        [
            rejected(
                "escapes",
                "repo://../x goes above the root of repo://; `..` cannot leave it"
            ),
            rejected(
                "escapes",
                "repo://leak resolves outside the root of repo:// through a symlink"
            ),
            rejected(
                "escapes",
                "skill://notes/../../x goes above the root of skill://; `..` cannot leave it"
            ),
            rejected(
                "arguments",
                "ssh:// reads run in a tool call (the call's output cap bounds them); there is none"
            ),
            rejected(
                "arguments",
                "ssh://-oProxyCommand=x/ does not name a host; write ssh://<host>/<path> with a host of letters, digits, `.`, `-`, `_` and `@` (set ports and options in ~/.ssh/config)"
            ),
            rejected(
                "escapes",
                "ssh://host/~/../etc/passwd goes above the root of ssh://; `..` cannot leave it"
            ),
            rejected(
                "scheme",
                "Unknown scheme sftp://; read serves agent://, skill://, memory://, mcp://, repo://, and ssh://"
            ),
            rejected("not_found", "Path 'skill://nope/SKILL.md' not found"),
            rejected("not_found", "this session has no chat memory"),
            rejected(
                "arguments",
                "agent:// reads the subagents of a tool call's conversation; there is none"
            ),
            rejected("arguments", "agent://<name|id> names one subagent"),
            rejected(
                "arguments",
                "mcp:// reads through the read tool; in the kernel, `await mcp.read_resource(server, uri)`"
            ),
        ]
    );
}
