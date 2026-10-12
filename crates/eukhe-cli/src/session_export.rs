//! `eukhe session export <session> [output]`: the HTML export of a saved
//! session -- a durable storage directory or a legacy `.jsonl` file (TS
//! main.ts' `--export` branch, reached through the `session export`
//! rewrite; the export itself is eukhe-core's `export_from_path`).

use eukhe_chord::context::BACKGROUND_CONTEXT;

use crate::args::Args;

/// Run the export and print the TS output: the written path on success
/// (`Exported to: ...`), the error message on failure (the main entry's
/// `Error: ...` prefix + exit 1).
pub fn run(parsed: &Args, agent_dir: &std::path::Path) -> Result<i32, String> {
    let Some(input) = parsed.export.as_deref() else {
        return Err("--export requires a value".to_string());
    };
    let output = parsed.messages.first().map(String::as_str);
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|error| format!("starting the export runtime: {error}"))?;
    let exported = runtime.block_on(eukhe_core::export_html::export_from_path(
        std::path::Path::new(input),
        output,
        agent_dir,
        &BACKGROUND_CONTEXT,
    ));
    match exported {
        Ok(path) => {
            println!("Exported to: {path}");
            Ok(0)
        }
        Err(error) => Err(format!("{error:#}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parsed_with(export: Option<&str>, messages: &[&str]) -> Args {
        crate::args::parse_args(&{
            let mut args: Vec<String> = Vec::new();
            if let Some(export) = export {
                args.push(crate::args::INTERNAL_RUNTIME_COMMAND_MARKER.to_string());
                args.push("--export".to_string());
                args.push(export.to_string());
            }
            args.extend(messages.iter().map(std::string::ToString::to_string));
            args
        })
    }

    /// A fixture session exports to the requested output and the run prints
    /// the TS success line.
    #[test]
    fn exports_a_session_file() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let input = dir.path().join("s.jsonl");
        std::fs::write(
            &input,
            concat!(
                r##"{"type":"session","id":"s","version":3,"timestamp":"2026-01-01T00:00:00.000Z","cwd":"/tmp"}"##,
                "\n",
                r##"{"type":"message","id":"e1","parentId":null,"timestamp":"2026-01-01T00:00:01.000Z","message":{"role":"user","content":"hi"}}"##,
                "\n",
            ),
        )
        .expect("write session");
        let out = dir.path().join("exported.html");
        let parsed = parsed_with(Some(input.to_str().unwrap()), &[out.to_str().unwrap()]);
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");
        let code = run(&parsed, &agent_dir).expect("export runs");
        assert_eq!(code, 0);
        assert!(out.exists());
    }

    /// A missing input file surfaces the TS error (through the main
    /// entry's `Error: ...` prefix).
    #[test]
    fn missing_file_errors() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let parsed = parsed_with(Some("/nonexistent/session.jsonl"), &[]);
        let error = run(&parsed, &dir.path().join("agent")).expect_err("missing file must fail");
        assert!(error.starts_with("File not found:"), "unexpected: {error}");
    }

    /// The session data an export file embeds, decoded.
    fn embedded_data(html: &str) -> serde_json::Value {
        use base64::Engine as _;
        let marker = "session-data\" type=\"application/json\">";
        let start = html.find(marker).expect("session data element");
        let blob = html[start + marker.len()..]
            .split('<')
            .next()
            .expect("script end");
        serde_json::from_slice(
            &base64::engine::general_purpose::STANDARD
                .decode(blob.trim())
                .expect("valid base64"),
        )
        .expect("valid json")
    }

    /// A durable session storage at `dir` (cwd `cwd`) asked `prompt` once,
    /// answered by the scripted faux provider with `answer`.
    fn durable_session(
        agent_dir: &std::path::Path,
        dir: &std::path::Path,
        cwd: &std::path::Path,
        prompt: &str,
        answer: &str,
    ) {
        use eukhe_ai::providers::faux_script::{create_faux_script_models, parse_faux_script};
        use eukhe_core::durable::{open_session, ModelRequest, SessionConfig, SessionStorage};
        use eukhe_durable::harness::types::InputSubmissionDraft;

        let script = parse_faux_script(&serde_json::json!({ "responses": [answer] }).to_string())
            .expect("faux script");
        let model = script.model.id.clone();
        let (models, _provider) = create_faux_script_models(script);
        let session_id = dir
            .file_name()
            .expect("session dir name")
            .to_string_lossy()
            .into_owned();
        let mut config = SessionConfig::new(
            agent_dir,
            cwd,
            &session_id,
            SessionStorage::Jsonl {
                dir: dir.to_path_buf(),
                fsync: true,
            },
        );
        config.models = Some(models);
        config.model = Some(ModelRequest {
            provider: Some("faux".to_owned()),
            pattern: model,
        });
        let cx = &BACKGROUND_CONTEXT;
        tokio::runtime::Builder::new_multi_thread()
            .worker_threads(2)
            .enable_all()
            .build()
            .expect("runtime")
            .block_on(async {
                let session = open_session(config, cx).await.expect("open session");
                session
                    .main()
                    .submit(InputSubmissionDraft::new(prompt), cx)
                    .await
                    .expect("submit")
                    .wait(cx)
                    .await
                    .expect("turn");
                session.close(cx).await.expect("close session");
            });
    }

    /// `session export <durable dir>` exports the stored conversation: the
    /// embedded rows carry the question and the answer, under a header
    /// naming the session and its cwd.
    #[test]
    fn exports_a_durable_session_dir() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        let cwd = dir.path().join("project");
        std::fs::create_dir_all(&cwd).expect("project dir");
        let storage = agent_dir.join("sessions").join("durable-1");
        durable_session(&agent_dir, &storage, &cwd, "hi", "hello there");
        let out = dir.path().join("exported.html");
        let parsed = parsed_with(Some(storage.to_str().unwrap()), &[out.to_str().unwrap()]);

        assert_eq!(run(&parsed, &agent_dir), Ok(0));

        let data = embedded_data(&std::fs::read_to_string(&out).expect("read export"));
        assert_eq!(
            (&data["header"]["id"], &data["header"]["cwd"]),
            (
                &serde_json::json!("durable-1"),
                &serde_json::json!(cwd.to_string_lossy())
            )
        );
        let messages: Vec<(String, String)> = data["entries"]
            .as_array()
            .expect("entries")
            .iter()
            .filter(|row| row["type"] == "message")
            .map(|row| {
                let message = &row["message"];
                let text = match &message["content"] {
                    serde_json::Value::String(text) => text.clone(),
                    content => content[0]["text"].as_str().unwrap_or_default().to_owned(),
                };
                (
                    message["role"].as_str().unwrap_or_default().to_owned(),
                    text,
                )
            })
            .collect();
        assert_eq!(
            messages,
            [
                ("user".to_owned(), "hi".to_owned()),
                ("assistant".to_owned(), "hello there".to_owned())
            ]
        );
    }

    /// A directory that holds no durable storage is an error naming it, and
    /// no export file is written.
    #[test]
    fn directory_without_storage_errors_without_output() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let input = dir.path().join("not-a-session");
        std::fs::create_dir_all(&input).expect("input dir");
        let out = dir.path().join("exported.html");
        let parsed = parsed_with(Some(input.to_str().unwrap()), &[out.to_str().unwrap()]);

        let error = run(&parsed, &dir.path().join("agent")).expect_err("must not export");

        assert_eq!(
            error,
            format!(
                "reading session storage {0}: no durable session storage at {0}",
                input.display()
            )
        );
        assert!(!out.exists(), "an export file was written");
    }
}
