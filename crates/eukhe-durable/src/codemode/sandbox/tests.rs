//! The sandbox's deterministic runs (pi-codemode `CodemodeSandboxBase.start()`
//! behaviour): calls, deliveries in `seq` order, the clock, timezone,
//! randomness, store, output, failures, the deadline, and aborts.

use eukhe_chord::json::JsonValue;
use indexmap::IndexMap;

use super::{
    CodemodeDeliverError, CodemodeRun, CodemodeRunEvent, CodemodeRunOptions, CodemodeSandbox,
    CodemodeSandboxOptions, CodemodeStartError,
};
use crate::codemode::types::{
    CodemodeCallTarget, CodemodeDeclaredGlobal, CodemodeDeclaredTool, CodemodeDuring,
    CodemodeEnding, CodemodeError, CodemodeErrorKind, CodemodeHostCall, CodemodeOutcome,
    CodemodeOutputItem, CodemodeResult, CodemodeStoreWrites, TextOrigin,
};

const STARTED_AT: f64 = 1_700_000_000_000.0;

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn tool(name: &str) -> CodemodeDeclaredTool {
    CodemodeDeclaredTool {
        name: name.to_owned(),
        js_name: crate::codemode::identifier::to_codemode_identifier(name),
        description: format!("{name} tool"),
    }
}

fn options() -> CodemodeRunOptions {
    CodemodeRunOptions {
        started_at: STARTED_AT,
        seed: 7,
        tools: vec![tool("echo"), tool("my-tool")],
        globals: vec![CodemodeDeclaredGlobal {
            name: "searchTools".to_owned(),
            spread: true,
        }],
        store: IndexMap::new(),
        timeout_ms: None,
    }
}

fn sandbox() -> CodemodeSandbox {
    CodemodeSandbox::new(CodemodeSandboxOptions::default())
}

fn start(code: &str, options: CodemodeRunOptions) -> CodemodeRun {
    sandbox().start(code, options).expect("the run starts")
}

/// Every event until `Finished`, answering nothing.
async fn events(run: &mut CodemodeRun) -> Vec<CodemodeRunEvent> {
    let mut events = Vec::new();
    while let Some(event) = run.next_event().await {
        let finished = matches!(event, CodemodeRunEvent::Finished(_));
        events.push(event);
        if finished {
            break;
        }
    }
    events
}

/// Run `code`, answering each call with `answer(call)` at clock `now`, and
/// return the calls made and the result.
async fn run_answering(
    code: &str,
    options: CodemodeRunOptions,
    mut answer: impl FnMut(&CodemodeHostCall) -> (f64, CodemodeOutcome),
) -> (Vec<CodemodeHostCall>, CodemodeResult) {
    let mut run = start(code, options);
    let handle = run.handle();
    let mut calls = Vec::new();
    let mut seq = 0;
    while let Some(event) = run.next_event().await {
        match event {
            CodemodeRunEvent::Started { .. } | CodemodeRunEvent::Idle { .. } => {}
            CodemodeRunEvent::Call(call) => {
                seq += 1;
                let (now, outcome) = answer(&call);
                handle.deliver(seq, now, call.id, &outcome).unwrap();
                calls.push(call);
            }
            CodemodeRunEvent::Finished(result) => return (calls, result),
        }
    }
    panic!("the run ended without a result");
}

fn completed(value: Option<JsonValue>) -> CodemodeEnding {
    CodemodeEnding::Completed {
        value,
        store_writes: CodemodeStoreWrites::default(),
    }
}

fn ok(value: &str) -> CodemodeOutcome {
    CodemodeOutcome::Ok {
        value: Some(json(value)),
    }
}

#[tokio::test]
async fn a_script_without_calls_reports_started_idle_and_its_value() {
    let sandbox = sandbox();
    let mut run = sandbox.start("return 1 + 2;", options()).unwrap();
    assert_eq!(
        events(&mut run).await,
        vec![
            CodemodeRunEvent::Started {
                fingerprint: sandbox.fingerprint().to_owned()
            },
            CodemodeRunEvent::Finished(CodemodeResult {
                ending: completed(Some(json("3"))),
                output: Vec::new(),
                during: Some(CodemodeDuring { seq: 0, issued: 0 }),
            }),
        ]
    );
}

#[tokio::test]
async fn calls_tools_and_globals_and_resumes_with_their_results() {
    let (calls, result) = run_answering(
        r#"const a = await tools.echo({ text: "hi" });
const b = await tools["my-tool"]({ n: 1 });
const c = await tools.my_tool({ n: 2 });
const found = await searchTools("files", { limit: 2 });
return [a, b, c, found];"#,
        options(),
        |call| (STARTED_AT, ok(&format!(r#""{}#{}""#, call.name, call.id))),
    )
    .await;
    assert_eq!(
        calls,
        vec![
            CodemodeHostCall {
                id: 1,
                target: CodemodeCallTarget::Tool,
                name: "echo".to_owned(),
                args: Some(json(r#"{"text":"hi"}"#)),
            },
            CodemodeHostCall {
                id: 2,
                target: CodemodeCallTarget::Tool,
                name: "my-tool".to_owned(),
                args: Some(json(r#"{"n":1}"#)),
            },
            CodemodeHostCall {
                id: 3,
                target: CodemodeCallTarget::Tool,
                name: "my-tool".to_owned(),
                args: Some(json(r#"{"n":2}"#)),
            },
            CodemodeHostCall {
                id: 4,
                target: CodemodeCallTarget::Global,
                name: "searchTools".to_owned(),
                args: Some(json(r#"["files",{"limit":2}]"#)),
            },
        ]
    );
    assert_eq!(
        result,
        CodemodeResult {
            ending: completed(Some(json(
                r#"["echo#1","my-tool#2","my-tool#3","searchTools#4"]"#
            ))),
            output: Vec::new(),
            during: Some(CodemodeDuring { seq: 4, issued: 4 }),
        }
    );
}

#[tokio::test]
async fn applies_results_in_seq_order_whatever_order_they_arrive_in() {
    let mut run = start(
        r"const [a, b] = await Promise.all([tools.echo({ n: 1 }), tools.echo({ n: 2 })]);
const order = [];
await Promise.all([
  tools.echo({ n: 3 }).then(() => order.push(3)),
  tools.echo({ n: 4 }).then(() => order.push(4)),
]);
return { a, b, order };",
        options(),
    );
    let handle = run.handle();
    let mut idles = Vec::new();
    let mut pending = Vec::new();
    let result = loop {
        match run.next_event().await.unwrap() {
            CodemodeRunEvent::Started { .. } => {}
            CodemodeRunEvent::Call(call) => pending.push(call.id),
            CodemodeRunEvent::Idle { seq, issued } => {
                idles.push((seq, issued));
                match seq {
                    // Result 2 (call 2) arrives before result 1 (call 1).
                    0 => {
                        handle
                            .deliver(2, STARTED_AT, 2, &ok(r#""second""#))
                            .unwrap();
                        handle.deliver(1, STARTED_AT, 1, &ok(r#""first""#)).unwrap();
                    }
                    // Call 4 answered first, as result 3.
                    2 => {
                        handle.deliver(3, STARTED_AT, 4, &ok("null")).unwrap();
                        handle.deliver(4, STARTED_AT, 3, &ok("null")).unwrap();
                    }
                    _ => {}
                }
            }
            CodemodeRunEvent::Finished(result) => break result,
        }
    };
    assert_eq!(pending, vec![1, 2, 3, 4]);
    assert_eq!(idles, vec![(0, 2), (1, 2), (2, 4), (3, 4)]);
    assert_eq!(
        result.ending,
        completed(Some(json(r#"{"a":"first","b":"second","order":[4,3]}"#)))
    );
}

#[tokio::test]
async fn refuses_deliveries_for_calls_not_waiting_and_reused_seqs() {
    let mut run = start("await tools.echo({}); await tools.echo({});", options());
    let handle = run.handle();
    let mut answered = false;
    let result = loop {
        match run.next_event().await.unwrap() {
            CodemodeRunEvent::Call(call) if !answered => {
                answered = true;
                assert_eq!(
                    handle.deliver(1, STARTED_AT, 9, &ok("1")),
                    Err(CodemodeDeliverError::NotWaiting(9))
                );
                assert_eq!(
                    handle.deliver(0, STARTED_AT, call.id, &ok("1")),
                    Err(CodemodeDeliverError::Seq(0))
                );
                assert_eq!(
                    handle.deliver(1, f64::NAN, call.id, &ok("1")),
                    Err(CodemodeDeliverError::Clock(1))
                );
                handle.deliver(1, STARTED_AT, call.id, &ok("1")).unwrap();
            }
            CodemodeRunEvent::Call(call) => {
                assert_eq!(
                    handle.deliver(1, STARTED_AT, call.id, &ok("1")),
                    Err(CodemodeDeliverError::Seq(1))
                );
                handle.deliver(2, STARTED_AT, call.id, &ok("2")).unwrap();
            }
            CodemodeRunEvent::Started { .. } | CodemodeRunEvent::Idle { .. } => {}
            CodemodeRunEvent::Finished(result) => break result,
        }
    };
    assert!(result.is_ok());
}

/// Everything a script can observe of time and randomness.
const OBSERVE: &str = r#"
const first = [Date.now(), new Date().toISOString(), Math.random(), Math.random()];
await tools.echo({});
const second = [Date.now(), String(new Date()), new Date(2020, 0, 2, 3, 4, 5).toISOString()];
await tools.echo({});
return {
  first,
  second,
  third: Date.now(),
  local: [
    new Date("2020-01-01T10:00").toISOString(),
    new Date("2020-01-01").toISOString(),
    new Date("2020-01-01T10:00:00+02:00").toISOString(),
    new Date("2020-07-01T10:00:00Z").toISOString(),
    Date.parse("Jan 1 2020 10:00"),
    Date.parse("Wed Jan 01 2020 10:00:00 GMT+0200 (CEST)"),
    new Date("12/25/2020").getTime(),
    new Date(Date.UTC(2020, 6, 1, 12)).getHours(),
    new Date(0).getTimezoneOffset(),
    new Date(0).toString(),
    new Date(0).toLocaleString(),
    typeof WeakRef,
    typeof FinalizationRegistry,
    typeof performance,
  ],
};
"#;

async fn observe(seed: u32, clocks: [f64; 2]) -> JsonValue {
    let mut index = 0;
    let options = CodemodeRunOptions { seed, ..options() };
    let (_, result) = run_answering(OBSERVE, options, |_| {
        let now = clocks[index.min(1)];
        index += 1;
        (now, ok("null"))
    })
    .await;
    match result.ending {
        CodemodeEnding::Completed { value, .. } => value.expect("a value"),
        CodemodeEnding::Failed(error) => panic!("the script failed: {error:?}"),
    }
}

#[tokio::test]
async fn time_timezone_and_randomness_are_virtual_utc_and_seeded() {
    let value = observe(7, [STARTED_AT + 5_000.0, STARTED_AT + 1_000.0]).await;
    let again = observe(7, [STARTED_AT + 5_000.0, STARTED_AT + 1_000.0]).await;
    let reseeded = observe(8, [STARTED_AT + 5_000.0, STARTED_AT + 1_000.0]).await;
    assert_eq!(value, again);
    assert_ne!(value["first"][2], reseeded["first"][2]);
    assert_eq!(value["first"][0], json("1700000000000"));
    assert_eq!(value["first"][1], json(r#""2023-11-14T22:13:20.000Z""#));
    // The clock reads the result's `now`, and never goes backwards.
    assert_eq!(value["second"][0], json("1700000005000"));
    assert_eq!(value["third"], json("1700000005000"));
    assert_eq!(
        value["second"][1],
        json(r#""Tue Nov 14 2023 22:13:25 GMT+0000 (Coordinated Universal Time)""#)
    );
    assert_eq!(value["second"][2], json(r#""2020-01-02T03:04:05.000Z""#));
    assert_eq!(
        value["local"],
        json(
            r#"["2020-01-01T10:00:00.000Z","2020-01-01T00:00:00.000Z","2020-01-01T08:00:00.000Z","2020-07-01T10:00:00.000Z",1577872800000,1577865600000,1608854400000,12,0,"Thu Jan 01 1970 00:00:00 GMT+0000 (Coordinated Universal Time)","1/1/1970, 12:00:00 AM","undefined","undefined","undefined"]"#
        )
    );
}

#[tokio::test]
async fn reads_the_store_and_reports_its_writes() {
    let mut store = IndexMap::new();
    store.insert("count".to_owned(), json("1"));
    store.insert("gone".to_owned(), json(r#"{"a":true}"#));
    let options = CodemodeRunOptions { store, ..options() };
    let (_, result) = run_answering(
        r#"store("count", load("count") + 1); store("gone", undefined); store("new", [load("gone")]); return load("count");"#,
        options,
        |_| (STARTED_AT, ok("null")),
    )
    .await;
    let mut set = IndexMap::new();
    set.insert("count".to_owned(), json("2"));
    set.insert("new".to_owned(), json("[null]"));
    assert_eq!(
        result.ending,
        CodemodeEnding::Completed {
            value: Some(json("2")),
            store_writes: CodemodeStoreWrites {
                set,
                delete: vec!["gone".to_owned()],
            },
        }
    );
}

#[tokio::test]
async fn keeps_text_console_and_image_output_in_order() {
    let (_, result) = run_answering(
        r#"text("a"); console.log("b", { c: 1 }); text({ d: 2 });
image("data:image/png;base64,iVBORw0KGgoAAAANSUhEUg==");
exit();
text("never");"#,
        options(),
        |_| (STARTED_AT, ok("null")),
    )
    .await;
    assert_eq!(
        result,
        CodemodeResult {
            ending: completed(None),
            output: vec![
                CodemodeOutputItem::Text {
                    text: "a".to_owned(),
                    origin: TextOrigin::Script
                },
                CodemodeOutputItem::Text {
                    text: r#"b {"c":1}"#.to_owned(),
                    origin: TextOrigin::Console
                },
                CodemodeOutputItem::Text {
                    text: r#"{"d":2}"#.to_owned(),
                    origin: TextOrigin::Script
                },
                CodemodeOutputItem::Image {
                    data: "iVBORw0KGgoAAAANSUhEUg==".to_owned(),
                    mime_type: "image/png".to_owned()
                },
            ],
            during: Some(CodemodeDuring { seq: 0, issued: 0 }),
        }
    );
}

#[tokio::test]
async fn a_rejection_carries_its_message_and_properties() {
    let (_, result) = run_answering(
        r"try { await tools.echo({}); } catch (error) { return [error.message, error.structuredOutput, error instanceof Error]; }",
        options(),
        |_| {
            (
                STARTED_AT,
                CodemodeOutcome::Err {
                    message: "boom".to_owned(),
                    properties: Some(
                        json(r#"{"structuredOutput":{"exitCode":1},"message":"ignored"}"#)
                            .as_object()
                            .unwrap()
                            .clone(),
                    ),
                },
            )
        },
    )
    .await;
    assert_eq!(
        result.ending,
        completed(Some(json(r#"["boom",{"exitCode":1},true]"#)))
    );
}

#[tokio::test]
async fn reports_thrown_errors_with_their_stack_and_syntax_errors() {
    let (_, thrown) = run_answering(
        "await tools.echo({});\nthrow new TypeError(\"bad\");",
        options(),
        |_| (STARTED_AT, ok("null")),
    )
    .await;
    let CodemodeEnding::Failed(error) = thrown.ending else {
        panic!("the script failed");
    };
    assert_eq!(
        (error.kind, error.name.as_deref(), error.message.as_str()),
        (CodemodeErrorKind::Script, Some("TypeError"), "bad")
    );
    let stack = error.stack.expect("a stack");
    assert!(stack.starts_with("TypeError: bad\n"), "{stack}");
    assert!(stack.contains("codemode.js:2"), "{stack}");
    assert!(!stack.contains("codemode-prelude.js"), "{stack}");
    assert_eq!(thrown.during, Some(CodemodeDuring { seq: 1, issued: 1 }));

    let mut run = start("return (", options());
    let Some(CodemodeRunEvent::Finished(result)) = events(&mut run).await.pop() else {
        panic!("a result");
    };
    let CodemodeEnding::Failed(error) = result.ending else {
        panic!("a syntax error");
    };
    assert_eq!(
        (error.kind, error.name.as_deref(), result.during),
        (CodemodeErrorKind::Script, Some("SyntaxError"), None)
    );
}

#[tokio::test]
async fn fails_a_script_that_waits_on_nothing() {
    let mut run = start("await new Promise(() => {});", options());
    let Some(CodemodeRunEvent::Finished(result)) = events(&mut run).await.pop() else {
        panic!("a result");
    };
    assert_eq!(
        result.ending,
        CodemodeEnding::Failed(CodemodeError {
            kind: CodemodeErrorKind::Script,
            name: Some("Error".to_owned()),
            message: "The script is waiting on a promise that can never settle: no tool call is pending, and timers do not exist here.".to_owned(),
            stack: None,
        })
    );
}

#[tokio::test]
async fn the_deadline_stops_a_busy_script() {
    let mut run = start(
        "while (true) {}",
        CodemodeRunOptions {
            timeout_ms: Some(50.0),
            ..options()
        },
    );
    let Some(CodemodeRunEvent::Finished(result)) = events(&mut run).await.pop() else {
        panic!("a result");
    };
    assert_eq!(
        result.ending,
        CodemodeEnding::Failed(CodemodeError {
            kind: CodemodeErrorKind::Timeout,
            name: None,
            message: "Execution timed out after 50 ms".to_owned(),
            stack: None,
        })
    );
}

#[tokio::test]
async fn an_abort_ends_a_waiting_script_and_closing_aborts_every_run() {
    let mut run = start("await tools.echo({});", options());
    let handle = run.handle();
    loop {
        if let CodemodeRunEvent::Call(_) = run.next_event().await.unwrap() {
            break;
        }
    }
    handle.abort("Stopped by the host");
    handle.abort("Second abort");
    let Some(CodemodeRunEvent::Finished(result)) = events(&mut run).await.pop() else {
        panic!("a result");
    };
    assert_eq!(
        result.ending,
        CodemodeEnding::Failed(CodemodeError {
            kind: CodemodeErrorKind::Aborted,
            name: None,
            message: "Stopped by the host".to_owned(),
            stack: None,
        })
    );
    assert!(handle.finished());

    let sandbox = sandbox();
    let mut run = sandbox.start("await tools.echo({});", options()).unwrap();
    sandbox.close();
    let Some(CodemodeRunEvent::Finished(result)) = events(&mut run).await.pop() else {
        panic!("a result");
    };
    let CodemodeEnding::Failed(error) = result.ending else {
        panic!("aborted");
    };
    assert_eq!(
        (error.kind, error.message.as_str()),
        (CodemodeErrorKind::Aborted, "Sandbox closed")
    );
    assert_eq!(
        sandbox.start("1", options()).err(),
        Some(CodemodeStartError::Closed)
    );
}

#[tokio::test]
async fn rejects_invalid_globals_and_duplicate_tools() {
    let with_globals = |names: &[&str]| CodemodeRunOptions {
        globals: names
            .iter()
            .map(|name| CodemodeDeclaredGlobal {
                name: (*name).to_owned(),
                spread: false,
            })
            .collect(),
        ..options()
    };
    let sandbox = sandbox();
    let error = |options| sandbox.start("1", options).err();
    assert_eq!(
        error(with_globals(&["tools"])),
        Some(CodemodeStartError::InvalidGlobal("tools".to_owned()))
    );
    assert_eq!(
        error(with_globals(&["a.b.c"])),
        Some(CodemodeStartError::InvalidGlobal("a.b.c".to_owned()))
    );
    assert_eq!(
        error(with_globals(&["models", "models.classify"])),
        Some(CodemodeStartError::GlobalNamespace("models".to_owned()))
    );
    assert_eq!(
        error(with_globals(&["x", "x"])),
        Some(CodemodeStartError::DuplicateGlobal("x".to_owned()))
    );
    assert_eq!(
        error(CodemodeRunOptions {
            tools: vec![tool("a-b"), tool("a_b")],
            ..options()
        }),
        Some(CodemodeStartError::DuplicateScriptName)
    );
}

#[tokio::test]
async fn unknown_tools_name_close_matches() {
    let mut run = start("await tools.ecko({});", options());
    let Some(CodemodeRunEvent::Finished(result)) = events(&mut run).await.pop() else {
        panic!("a result");
    };
    let CodemodeEnding::Failed(error) = result.ending else {
        panic!("a script error");
    };
    assert_eq!(
        error.message,
        "tools.ecko does not exist. Available: echo, my_tool. ALL_TOOLS lists every tool; searchTools(query) finds tools by topic. Check for a member with \"ecko\" in tools."
    );
}

#[test]
fn the_engine_in_the_fingerprint_is_the_locked_rquickjs() {
    let lock = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../../Cargo.lock"))
        .expect("read Cargo.lock");
    let version = lock
        .split("[[package]]")
        .find(|package| package.contains("\nname = \"rquickjs\"\n"))
        .and_then(|package| {
            package
                .lines()
                .find_map(|line| line.strip_prefix("version = \""))
                .map(|version| version.trim_end_matches('"').to_owned())
        })
        .expect("rquickjs in Cargo.lock");
    assert_eq!(super::ENGINE, format!("rquickjs {version}"));
}
