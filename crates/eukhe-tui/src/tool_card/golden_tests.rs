//! Pins the rendered rows of every tool card shape against a fixture: each
//! card kind and status at three widths and every detail level, as ANSI.

use std::fmt::Write as _;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

use super::{render_tool_card, ToolCallCard, ToolResultView};
use crate::chat::Detail;
use crate::theme::{ColorMode, Theme};

const WIDTHS: [usize; 3] = [40, 80, 120];
const DETAILS: [Detail; 3] = [Detail::Overview, Detail::Details, Detail::All];
const FRAMES: [usize; 2] = [0, 7];

/// The run state a fixture card is in.
enum Phase {
    Queued,
    Running,
    Done,
    Error,
}

fn card(name: &str, args: Value, phase: &Phase, text: &str, details: Value) -> ToolCallCard {
    let start = Instant::now();
    let content = if text.is_empty() {
        Vec::new()
    } else {
        vec![json!({ "type": "text", "text": text })]
    };
    let result = ToolResultView {
        content,
        details,
        is_error: matches!(phase, Phase::Error),
    };
    let (started, result, result_partial) = match phase {
        Phase::Queued => (false, None, false),
        Phase::Running => (true, Some(result), true),
        Phase::Done | Phase::Error => (true, Some(result), false),
    };
    ToolCallCard {
        id: "toolu_golden".into(),
        name: name.into(),
        args,
        started,
        started_at: started.then_some(start),
        ended_at: started.then_some(start + Duration::from_millis(1234)),
        result,
        result_partial,
        aborted: false,
    }
}

fn png(width: u32, height: u32) -> String {
    use base64::Engine;
    let mut bytes = vec![0x89, b'P', b'N', b'G'];
    bytes.extend(vec![0u8; 12]);
    bytes.extend(width.to_be_bytes());
    bytes.extend(height.to_be_bytes());
    base64::engine::general_purpose::STANDARD.encode(bytes)
}

fn with_image(mut card: ToolCallCard) -> ToolCallCard {
    if let Some(result) = card.result.as_mut() {
        result
            .content
            .push(json!({ "type": "image", "data": png(64, 32), "mimeType": "image/png" }));
    }
    card
}

fn ipython_cases() -> Vec<(&'static str, ToolCallCard)> {
    let code = json!({ "code": "for i in range(3):\n    print(f'line {i}')" });
    let ok = json!({ "status": "ok", "durationMs": 3 });
    let long_code = json!({
        "code": "values = [compute_something_rather_long(index, factor=2) for index in range(100)]\nprint(values)"
    });
    vec![
        ("ipython queued", card("ipython", code.clone(), &Phase::Queued, "", Value::Null)),
        ("ipython queued no code", card("ipython", json!({}), &Phase::Queued, "", Value::Null)),
        ("ipython running", card("ipython", code.clone(), &Phase::Running, "", json!({ "status": "ok" }))),
        ("ipython running output", card("ipython", code.clone(), &Phase::Running, "line 0\n", json!({ "status": "ok" }))),
        ("ipython done", card("ipython", code.clone(), &Phase::Done, "line 0\nline 1\n\nline 2\n", ok.clone())),
        ("ipython done no output", card("ipython", json!({ "code": "x = 1" }), &Phase::Done, "", ok.clone())),
        (
            "ipython error traceback",
            card(
                "ipython",
                json!({ "code": "print('before')\nraise ValueError('boom')" }),
                &Phase::Error,
                "before\nTraceback (most recent call last):\n  File \"<cell>\", line 2\nValueError: boom",
                json!({ "status": "error", "durationMs": 9, "error": { "ename": "ValueError", "evalue": "boom" } }),
            ),
        ),
        (
            "ipython error summary",
            card(
                "ipython",
                json!({ "code": "raise ValueError('boom')" }),
                &Phase::Error,
                "",
                json!({ "status": "error", "error": { "ename": "ValueError", "evalue": "boom" } }),
            ),
        ),
        ("ipython error stderr", card("ipython", json!({ "code": "fail()" }), &Phase::Error, "stderr says no\nsecond", json!({}))),
        ("ipython aborted", card("ipython", code, &Phase::Done, "line 0\n", json!({ "status": "aborted", "durationMs": 40 }))),
        ("ipython bash cell", card("ipython", json!({ "code": "%%bash\necho hi\nls -la" }), &Phase::Done, "hi\n", json!({ "status": "ok", "durationMs": 8 }))),
        ("ipython magic", card("ipython", json!({ "code": "!ls -la\nx = 1\nprint(x)" }), &Phase::Done, "1\n", ok.clone())),
        ("ipython long", card("ipython", long_code, &Phase::Done, &format!("[{}]", "0, 2, 4, 6, 8, 10, 12, 14, 16, 18, ".repeat(6)), ok.clone())),
        (
            "ipython sent messages",
            card(
                "ipython",
                json!({ "code": "await agent_message.send(\"Ping.\", receiver_role=\"parent\")" }),
                &Phase::Done,
                "",
                json!({
                    "status": "ok",
                    "durationMs": 3,
                    "sentAgentMessages": [{
                        "id": "agentmsg_1",
                        "message": "Ping.\nThen report back with a rather long sentence that has to wrap somewhere.",
                        "deliveryStatus": "delivered",
                        "receiverRole": "parent",
                        "target": { "activeSessionId": "worker-active", "sessionId": "worker-session", "sessionName": "Worker" },
                    }, {
                        "id": "agentmsg_2",
                        "message": "Queued one.",
                        "deliveryStatus": "queued",
                        "target": { "sessionId": "peer-session-with-a-very-long-identifier-0123456789" },
                    }],
                }),
            ),
        ),
        ("ipython images", with_image(card("ipython", json!({ "code": "display(img)" }), &Phase::Done, "shown", ok))),
        (
            "ipython background exit",
            card(
                "ipython",
                json!({ "code": "h = bash('sleep 0.1')" }),
                &Phase::Done,
                "",
                json!({ "status": "ok", "durationMs": 12, "result": "<BashHandle pid=421 exit_code=1 command='sleep 0.1'>" }),
            ),
        ),
        (
            "ipython background running",
            card(
                "ipython",
                json!({ "code": "h = bash('sleep 0.1')" }),
                &Phase::Done,
                "",
                json!({ "status": "ok", "durationMs": 12, "result": "<BashHandle pid=421 running command='sleep 0.1'>" }),
            ),
        ),
        (
            "ipython bash dominated",
            card(
                "ipython",
                json!({ "code": "r = await sh(\"\"\"\ncd crates/eukhe-tui\ncargo test -p eukhe-tui\n\"\"\")\nprint(r.output)" }),
                &Phase::Done,
                "ok\n",
                json!({
                    "status": "ok",
                    "durationMs": 2,
                    "bashCommands": { "first": "\ncd crates/eukhe-tui\ncargo test -p eukhe-tui\n", "count": 3, "lines": 4 },
                }),
            ),
        ),
    ]
}

fn bash_cases() -> Vec<(&'static str, ToolCallCard)> {
    let seq = (1..=12)
        .map(|n| n.to_string())
        .collect::<Vec<_>>()
        .join("\n");
    let command = json!({ "script": "seq 1 12", "timeout": 30 });
    vec![
        (
            "bash queued",
            card("bash", command.clone(), &Phase::Queued, "", Value::Null),
        ),
        (
            "bash running",
            card("bash", command.clone(), &Phase::Running, "1\n2", json!({})),
        ),
        (
            "bash running empty",
            card("bash", command.clone(), &Phase::Running, "", json!({})),
        ),
        (
            "bash done",
            card("bash", command, &Phase::Done, &seq, json!({})),
        ),
        (
            "bash error",
            card(
                "bash",
                json!({ "script": "false" }),
                &Phase::Error,
                "boom\nexit 1",
                json!({}),
            ),
        ),
        (
            "bash truncated lines",
            card(
                "bash",
                json!({ "script": "cat big.txt" }),
                &Phase::Done,
                "line1\nline2",
                json!({
                    "truncation": { "truncated": true, "truncatedBy": "lines", "outputLines": 2, "totalLines": 10 },
                    "fullOutputPath": "/tmp/pi-bash-abc-with-a-long-name-for-wrapping",
                }),
            ),
        ),
        (
            "bash truncated bytes",
            card(
                "bash",
                json!({ "script": "cat big.bin" }),
                &Phase::Done,
                "x",
                json!({ "truncation": { "truncated": true, "truncatedBy": "bytes", "outputLines": 3, "totalLines": 9 } }),
            ),
        ),
        (
            "bash invalid",
            card(
                "bash",
                json!({ "script": 5 }),
                &Phase::Queued,
                "",
                Value::Null,
            ),
        ),
        (
            "bash empty",
            card(
                "bash",
                json!({ "script": "" }),
                &Phase::Queued,
                "",
                Value::Null,
            ),
        ),
        (
            "bash python",
            card(
                "bash",
                json!({ "script": "python3 -c \"print(1)\"" }),
                &Phase::Done,
                "1",
                json!({}),
            ),
        ),
        (
            "bash long",
            card(
                "bash",
                json!({ "script": "find . -name '*.rs' -not -path './target/*' -exec grep -l 'render_tool_card' {} +" }),
                &Phase::Done,
                &format!(
                    "{}\nshort\n{}",
                    "a/very/long/path/".repeat(8),
                    "word ".repeat(30)
                ),
                json!({}),
            ),
        ),
        (
            "bash images",
            with_image(card(
                "bash",
                json!({ "script": "screenshot" }),
                &Phase::Done,
                "saved",
                json!({}),
            )),
        ),
    ]
}

fn generic_cases() -> Vec<(&'static str, ToolCallCard)> {
    let args = json!({ "path": "src/lib.rs", "limit": 20, "offset": 4 });
    let output = "one\ntwo\nthree\nfour\nfive";
    vec![
        (
            "generic queued",
            card("read", args.clone(), &Phase::Queued, "", Value::Null),
        ),
        (
            "generic running",
            card("read", args.clone(), &Phase::Running, "one", json!({})),
        ),
        (
            "generic done",
            card("read", args.clone(), &Phase::Done, output, json!({})),
        ),
        (
            "generic done short",
            card("read", json!({ "a": 1 }), &Phase::Done, "ok", json!({})),
        ),
        (
            "generic error",
            card(
                "read",
                args,
                &Phase::Error,
                "no such file: src/lib.rs",
                json!({}),
            ),
        ),
        (
            "generic empty args",
            card("custom", Value::Null, &Phase::Done, "", json!({})),
        ),
        (
            "generic long",
            card(
                "custom",
                json!({ "query": "a long query ".repeat(12) }),
                &Phase::Done,
                &"x".repeat(150),
                json!({}),
            ),
        ),
        (
            "generic edit",
            card(
                "edit",
                json!({ "input": "[src/media.ts#AA10]\nPUT >45:\n+  \"heph-forge\": {\n+    width: 2952,\n+  },\nCUT 50.=51", "i": "Registering the wallpaper" }),
                &Phase::Done,
                "[src/media.ts#2F60]\n38:  \"ben-davis-site-tour\": {\n... 11 more lines",
                json!({}),
            ),
        ),
        (
            "generic grep",
            card(
                "grep",
                json!({ "pattern": "fn main", "path": "src", "i": "Finding main" }),
                &Phase::Done,
                "[src/main.rs#1234]\n*1:fn main() {}",
                json!({}),
            ),
        ),
        (
            "generic images",
            with_image(card("custom", json!({}), &Phase::Done, "done", json!({}))),
        ),
    ]
}

/// Every case at every width, detail level, frame and image setting; a
/// variant that renders exactly like an earlier one of the same case and
/// width names that variant instead of repeating its rows.
fn render_matrix() -> String {
    let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
    let mut out = String::new();
    let cases = ipython_cases()
        .into_iter()
        .chain(bash_cases())
        .chain(generic_cases());
    for (name, card) in cases {
        for width in WIDTHS {
            let mut seen: Vec<(String, String)> = Vec::new();
            for detail in DETAILS {
                for frame in FRAMES {
                    for show_images in [true, false] {
                        let key = format!(
                            "{name} width={width} detail={detail:?} frame={frame} images={show_images}"
                        );
                        let mut rows = String::new();
                        for row in
                            render_tool_card(&card, frame, detail, &theme, width, show_images)
                        {
                            let _ = writeln!(rows, "{:?}", crate::ansi::line_to_ansi(&row));
                        }
                        if let Some((earlier, _)) =
                            seen.iter().find(|(_, earlier)| *earlier == rows)
                        {
                            let _ = writeln!(out, "## {key} = {earlier}");
                        } else {
                            let _ = write!(out, "## {key}\n{rows}");
                            seen.push((key, rows));
                        }
                    }
                }
            }
        }
    }
    out
}

#[test]
fn tool_cards_render_the_pinned_rows() {
    assert_eq!(render_matrix(), include_str!("golden.txt"));
}
