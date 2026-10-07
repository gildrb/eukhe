//! `read` cases of `test/tools.test.ts`.

use std::io::Write;
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::from_json;
use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::json;

use super::support::{
    diagnostic_text, native, run, temp_dir, text_output, write_file, FakeApi, HookedEnv,
};
use crate::env::{BinaryReader, FileError, FileInfo, FileSystem, LineRange, LineScan};
use crate::tools::create_read_tool;

fn lines(count: usize, prefix: &str) -> String {
    (1..=count)
        .map(|index| format!("{prefix}{index}"))
        .collect::<Vec<_>>()
        .join("\n")
}

#[tokio::test]
async fn fail_with_an_ordinary_error_when_no_environment_is_configured() {
    let api = FakeApi::new(None);
    let error = super::support::execute(
        &create_read_tool(),
        json!({ "path": "x" }),
        &api,
        &BACKGROUND_CONTEXT,
    )
    .await
    .unwrap_err();
    assert!(error.to_string().contains("No execution environment"));
}

#[tokio::test]
async fn reads_text_with_offsets_and_limits_and_reports_continuation_as_a_diagnostic() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    write_file(env.as_ref(), "test.txt", lines(100, "Line ")).await;
    let (result, _) = run(
        &create_read_tool(),
        json!({ "path": "test.txt", "offset": 41, "limit": 20 }),
        env,
    )
    .await;
    let result = result.unwrap();
    let output = text_output(&result);
    assert!(!output.contains("Line 40"));
    assert!(output.contains("Line 41"));
    assert!(output.contains("Line 60"));
    assert!(!output.contains("Line 61"));
    assert!(!output.contains("more lines"));
    assert_eq!(
        diagnostic_text(&result),
        "40 more lines in file. Use offset=61 to continue."
    );
}

#[tokio::test]
async fn truncates_large_text_by_line_count() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    write_file(env.as_ref(), "large.txt", lines(2500, "Line ")).await;
    let (result, _) = run(&create_read_tool(), json!({ "path": "large.txt" }), env).await;
    let result = result.unwrap();
    assert_eq!(
        diagnostic_text(&result),
        "Showing lines 1-2000 of 2500. Use offset=2001 to continue."
    );
    assert_eq!(
        result.diagnostics.as_ref().unwrap()[0].code.as_deref(),
        Some("truncated")
    );
    let details: serde_json::Value = from_json(result.details.as_ref().unwrap()).unwrap();
    assert_eq!(
        details["truncation"],
        json!({
            "truncated": true,
            "truncatedBy": "lines",
            "totalLines": 2500,
            "totalBytes": details["truncation"]["totalBytes"],
            "outputLines": 2000,
            "outputBytes": details["truncation"]["outputBytes"],
            "lastLinePartial": false,
            "firstLineExceedsLimit": false,
            "maxLines": 2000,
            "maxBytes": 51200
        })
    );
}

#[tokio::test]
async fn does_not_count_a_trailing_newline_as_an_extra_line_at_the_truncation_limit() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    write_file(
        env.as_ref(),
        "exact.txt",
        format!("{}\n", vec!["x"; 2000].join("\n")),
    )
    .await;
    let (result, _) = run(&create_read_tool(), json!({ "path": "exact.txt" }), env).await;
    let result = result.unwrap();
    assert_eq!(result.details, None);
    assert_eq!(result.diagnostics, Some(Vec::new()));
}

#[tokio::test]
async fn shows_the_start_of_a_line_longer_than_the_byte_limit() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    write_file(
        env.as_ref(),
        "long.txt",
        format!("{}\nnext\n", "é".repeat(40_000)),
    )
    .await;
    let (result, _) = run(&create_read_tool(), json!({ "path": "long.txt" }), env).await;
    let result = result.unwrap();
    // Two-byte characters: the cut lands on a character boundary at or below the limit.
    assert_eq!(text_output(&result), "é".repeat(25_600));
    assert_eq!(
        diagnostic_text(&result),
        "Line 1 is 78.1KB, exceeds the 50.0KB limit; showing its first 50.0KB. Use bash: sed -n '1p' long.txt | tail -c +51201"
    );
    let details: serde_json::Value = from_json(result.details.as_ref().unwrap()).unwrap();
    let truncation = &details["truncation"];
    assert_eq!(truncation["truncated"], json!(true));
    assert_eq!(truncation["firstLineExceedsLimit"], json!(true));
    assert_eq!(truncation["outputBytes"], json!(51_200));
    assert_eq!(truncation["outputLines"], json!(1));
    assert!(truncation.get("content").is_none());
}

#[tokio::test]
async fn rejects_offsets_beyond_the_file() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    write_file(env.as_ref(), "short.txt", "one\ntwo\nthree").await;
    let (result, _) = run(
        &create_read_tool(),
        json!({ "path": "short.txt", "offset": 100 }),
        env,
    )
    .await;
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("Offset 100 is beyond end of file (3 lines total)"));
}

/// A reader that appends to the log before every read, as a busy writer
/// would.
struct GrowingReader {
    inner: Box<dyn BinaryReader>,
    log: std::path::PathBuf,
}

impl BinaryReader for GrowingReader {
    fn info<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<FileInfo, FileError>> {
        self.inner.info(cx)
    }

    fn read<'a>(
        &'a self,
        offset: f64,
        length: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<u8>, FileError>> {
        let mut file = std::fs::OpenOptions::new()
            .append(true)
            .open(&self.log)
            .expect("open log");
        file.write_all(b"more\n").expect("append log");
        self.inner.read(offset, length, cx)
    }

    fn scan_lines<'a>(
        &'a self,
        range: LineRange,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<LineScan, FileError>> {
        self.inner.scan_lines(range, cx)
    }

    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()> {
        self.inner.close(cx)
    }
}

#[tokio::test]
async fn reads_a_log_that_grows_while_it_is_read() {
    let dir = temp_dir();
    let log = dir.path().join("app.log");
    let mut env = HookedEnv::new(native(&dir));
    write_file(&env, "app.log", "one\ntwo\n").await;
    env.open_binary_reader = Some(Arc::new(move |inner, path, options, cx| {
        let log = log.clone();
        async move {
            let reader = inner.open_binary_reader(path, options, cx).await?;
            Ok(Box::new(GrowingReader { inner: reader, log }) as Box<dyn BinaryReader>)
        }
        .boxed()
    }));
    let (result, _) = run(
        &create_read_tool(),
        json!({ "path": "app.log", "limit": 2 }),
        Arc::new(env),
    )
    .await;
    assert_eq!(text_output(&result.unwrap()), "one\ntwo");
}

#[tokio::test]
async fn reports_images_by_content_as_unsupported() {
    let dir = temp_dir();
    let env = Arc::new(native(&dir));
    // The base64 PNG of the TS test, decoded.
    let png: [u8; 70] = [
        0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a, 0x00, 0x00, 0x00, 0x0d, 0x49, 0x48, 0x44,
        0x52, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x08, 0x06, 0x00, 0x00, 0x00, 0x1f,
        0x15, 0xc4, 0x89, 0x00, 0x00, 0x00, 0x0d, 0x49, 0x44, 0x41, 0x54, 0x78, 0x9c, 0x63, 0x60,
        0x60, 0x60, 0xf8, 0x0f, 0x00, 0x01, 0x04, 0x01, 0x00, 0x5f, 0xe5, 0xc3, 0x4b, 0x00, 0x00,
        0x00, 0x00, 0x49, 0x45, 0x4e, 0x44, 0xae, 0x42, 0x60, 0x82,
    ];
    write_file(env.as_ref(), "image.txt", png).await;
    let (result, _) = run(&create_read_tool(), json!({ "path": "image.txt" }), env).await;
    let result = result.unwrap();
    assert_eq!(result.content, Some(Vec::new()));
    assert_eq!(result.is_error, Some(true));
    assert_eq!(
        diagnostic_text(&result),
        "image.txt is an image (image/png); reading images is not supported"
    );
}
