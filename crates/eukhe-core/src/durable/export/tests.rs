//! `session export` over durable storages: the CLI path
//! ([`crate::export_html::export_from_path`]) reads a storage through
//! [`read_export_data`] and embeds exactly the rows [`export_rows`] maps.

use std::path::Path;

use serde_json::{json, Value};

use super::*;
use crate::durable::discovery::tests::{cx, fixture};
use crate::durable::import_legacy_session;
use crate::export_html::export_from_path;
use crate::export_html::tests::embedded_data;

/// `(role, text)` of every exported `message` row.
fn message_texts(entries: &Value) -> Vec<(String, String)> {
    entries
        .as_array()
        .expect("entries")
        .iter()
        .filter(|row| row["type"] == "message")
        .map(|row| {
            let message = &row["message"];
            let text = match &message["content"] {
                Value::String(text) => text.clone(),
                content => content[0]["text"].as_str().unwrap_or_default().to_owned(),
            };
            (
                message["role"].as_str().unwrap_or_default().to_owned(),
                text,
            )
        })
        .collect()
}

async fn export_to(input: &Path, out: &Path) -> anyhow::Result<String> {
    export_from_path(
        input,
        Some(out.to_str().expect("utf-8")),
        &eukhe_theme::Palette::default_theme(crate::theme_rules::THEME_RULES),
        cx(),
    )
    .await
}

/// A durable storage directory exports its main conversation: the header
/// names the session and its cwd, and the rows are the history's export
/// rows (the question and the answer among them).
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn durable_dir_exports_its_messages() {
    let fixture = fixture();
    let cwd = fixture.project("alpha");
    let entries = fixture.durable("durable-1", &cwd, &["hi"]).await;
    let out = fixture.project("out").join("export.html");

    export_to(&fixture.sessions.join("durable-1"), &out)
        .await
        .expect("export");

    let data = embedded_data(&std::fs::read_to_string(&out).expect("read export"));
    assert_eq!(
        message_texts(&data["entries"]),
        [
            ("user".to_owned(), "hi".to_owned()),
            ("assistant".to_owned(), "answer 1".to_owned())
        ]
    );
    let rows = export_rows(&entries).expect("rows");
    let mut header = export_header("durable-1", &cwd.to_string_lossy());
    header["timestamp"] = data["header"]["timestamp"].clone();
    assert_eq!(
        data,
        json!({ "header": header, "entries": rows.entries, "leafId": rows.leaf_id })
    );
}

/// A legacy file whose storage exists exports the storage (the session
/// since its import), not the stale file.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn imported_legacy_file_exports_its_storage() {
    let fixture = fixture();
    let cwd = fixture.project("alpha");
    let legacy = fixture.legacy("legacy-1", &cwd);
    import_legacy_session(&legacy, &fixture.sessions.join("legacy-1"), cx())
        .await
        .expect("import");
    let out = fixture.project("out").join("export.html");

    export_to(&legacy, &out).await.expect("export");

    let data = embedded_data(&std::fs::read_to_string(&out).expect("read export"));
    assert_eq!(data["header"]["id"], "legacy-1");
    assert_eq!(
        message_texts(&data["entries"]),
        [
            ("user".to_owned(), "legacy question".to_owned()),
            ("assistant".to_owned(), "legacy answer".to_owned())
        ]
    );
}

/// A directory without a durable storage is an error naming it, and no
/// export file is written.
#[tokio::test]
async fn directory_without_storage_errors_without_output() {
    let fixture = fixture();
    let dir = fixture.project("not-a-session");
    let out = fixture.project("out").join("export.html");

    let error = export_to(&dir, &out)
        .await
        .expect_err("a directory without a storage must not export");

    assert_eq!(
        format!("{error:#}"),
        format!(
            "reading session storage {0}: no durable session storage at {0}",
            dir.display()
        )
    );
    assert!(!out.exists(), "an export file was written");
}

/// A storage whose history has nothing to export (opened, never asked) is
/// an error, and no export file is written.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn empty_storage_errors_without_output() {
    let fixture = fixture();
    let cwd = fixture.project("alpha");
    fixture.durable("empty-1", &cwd, &[]).await;
    let dir = fixture.sessions.join("empty-1");
    let out = fixture.project("out").join("export.html");

    let error = export_to(&dir, &out)
        .await
        .expect_err("an empty session must not export");

    assert_eq!(
        format!("{error:#}"),
        format!("Session has no entries to export: {}", dir.display())
    );
    assert!(!out.exists(), "an export file was written");
}

/// An engine's own input exports as a hidden `custom_message` (the HTML
/// view skips `display: false` rows), with its origin; a re-import gives
/// it back to the model as user input. The user's prompt stays a message.
#[test]
fn engine_inputs_export_as_hidden_custom_messages() {
    let record = |id: u64, text: &str, origin: Option<Value>| -> EntryRecord {
        let mut entry = json!({
            "kind": "pi.user", "id": id, "conversationId": 1,
            "model": [{ "role": "user", "content": [{ "type": "text", "text": text }], "timestamp": id }],
        });
        if let Some(origin) = origin {
            entry["data"] = json!({ "origin": origin });
        }
        serde_json::from_value(entry).expect("entry")
    };
    let origin = json!({ "kind": "autonomous", "nudge": "continuation" });
    let rows = export_rows(&[
        record(1, "optimize the parser", None),
        record(
            2,
            "[autonomous-continuation]\n\ncontinue",
            Some(origin.clone()),
        ),
    ])
    .expect("export");
    let entries = Value::Array(rows.entries);
    assert_eq!(
        message_texts(&entries),
        [("user".to_owned(), "optimize the parser".to_owned())]
    );
    let hidden = &entries[1];
    assert_eq!(hidden["type"], "custom_message");
    assert_eq!(hidden["customType"], "autonomous_continuation");
    assert_eq!(hidden["display"], false);
    assert_eq!(hidden["details"]["origin"], origin);
    assert_eq!(
        hidden["content"][0]["text"],
        "[autonomous-continuation]\n\ncontinue"
    );
    // The legacy import makes it a model-visible custom entry again.
    let draft = crate::durable::custom_entry_draft(
        "autonomous_continuation",
        eukhe_types::pi_ai::UserContent::Text("continue".to_owned()),
        false,
        None,
        2,
    )
    .expect("draft");
    assert!(draft.model.is_some(), "the model reads the imported row");
}
