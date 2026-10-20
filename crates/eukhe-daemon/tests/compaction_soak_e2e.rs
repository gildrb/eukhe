//! Compaction soak: 300+ turns through the real daemon on a small context
//! window with a small reserve, so the compaction threshold crosses again
//! and again, mixing tool calls, steering and follow-ups sent while the
//! session is busy, and one context-overflow recovery.
//!
//! The provider is a scripted OpenAI-compatible mock that enforces the
//! window itself: any request over it gets the provider's context-overflow
//! error, so "no overflow" is the provider's verdict, not the client's
//! estimate. Over the whole run: no compaction fails, no turn stalls (each
//! settles while the session or the provider keeps making progress), no
//! request overflows except the one the script injects (which the session
//! recovers from by compacting), the durable transcript holds every
//! prompt once with strictly increasing entry ids, and more than 20
//! compactions committed.
#![allow(clippy::too_many_lines)]
#![allow(clippy::cast_possible_truncation)]

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "../../eukhe-cli/tests/support/durable_store.rs"]
mod durable_store;
#[path = "support/isolated_supervisor.rs"]
mod isolated_supervisor;
#[path = "support/mock_llm.rs"]
mod mock_llm;
#[path = "support/process.rs"]
mod process;
#[path = "support/wire_client.rs"]
mod wire_client;

use isolated_supervisor::Supervisor;
use mock_llm::{MockLlm, Reply, RequestKind, Served};
use wire_client::WireClient;

const MODEL: &str = "mock-1";

/// Turns the soak runs (prompts; steers and follow-ups come on top).
const TURNS: usize = 300;

/// Room over the fixed request overhead (system prompt and tools): the
/// conversation itself gets this many tokens of the window.
const ROOM: u64 = 6_000;
const RESERVE: u64 = 1_500;
const KEEP_RECENT: u64 = 400;

/// Filler words per turn (` wN`: about one token each).
const PAD: usize = 400;

/// No progress at all (no daemon line, no provider activity) for this long
/// is a stalled turn.
const STALL: Duration = Duration::from_secs(60);

const TOOL: &str = "[tool]";
const BUSY: &str = "[busy]";
const OVERFLOW: &str = "[overflow]";

fn tag(prompt: &str) -> String {
    prompt
        .split_whitespace()
        .next()
        .unwrap_or_default()
        .to_string()
}

fn answer_for(prompt: &str) -> String {
    format!("answer to {}", tag(prompt))
}

/// The script: a summary for the summarizer; for a turn, a quick `ipython`
/// call first when tagged [`TOOL`], an answer held on the turn's own gate
/// when tagged [`BUSY`], one overflow error for the first request of a
/// turn tagged [`OVERFLOW`] that still carries an earlier answer, else the
/// answer. The call after a tool
/// answers the prompt its call id names: a compaction between the call
/// and that request may have folded the prompt into the summary.
fn script(request: &mock_llm::Request, overflowed: &AtomicBool) -> Reply {
    match request.kind {
        RequestKind::Summarizer => Reply::text(
            "## Goal\nKeep answering the soak's numbered prompts.\n## Progress\nEarlier prompts answered.",
        ),
        RequestKind::MemoryNode => Reply::text("A soak line."),
        RequestKind::Turn => {
            let prompt = &request.prompt;
            if request.after_tool {
                let call = request.tool_results.last().expect("a tool result");
                Reply::text(answer_for(call.strip_prefix("call-").unwrap_or(call)))
            } else if prompt.contains(OVERFLOW)
                && carries_an_earlier_answer(&request.body)
                && !overflowed.swap(true, Ordering::SeqCst)
            {
                Reply::overflow()
            } else if prompt.contains(TOOL) {
                Reply::tool_call(
                    format!("call-{}", tag(prompt)),
                    "ipython",
                    json!({ "code": "print(6 * 7)" }),
                )
            } else if prompt.contains(BUSY) {
                Reply::text(answer_for(prompt)).held(tag(prompt))
            } else {
                Reply::text(answer_for(prompt))
            }
        }
    }
}

/// Whether a turn request still carries an answer from an earlier turn: an
/// overflow compaction can then cut it. Right after a threshold compaction a
/// request holds only the summary and the new prompt, which nothing can
/// shrink, so an overflow injected there could never recover.
fn carries_an_earlier_answer(body: &Value) -> bool {
    body["messages"].as_array().is_some_and(|messages| {
        messages.iter().any(|message| {
            message["role"] == "assistant" && message["content"].to_string().contains("answer to ")
        })
    })
}

fn padded(tag: &str, marks: &[&str]) -> String {
    let mut text = tag.to_string();
    for mark in marks {
        text.push(' ');
        text.push_str(mark);
    }
    for index in 0..PAD {
        let _ = write!(text, " w{index}");
    }
    text
}

/// Wait for the response to `id` while anything moves ([`settle_until`]).
fn settle(client: &WireClient, mock: &MockLlm, id: &str, what: &str) -> Value {
    settle_until(client, mock, what, || client.try_response(id))
}

/// Wait until `done` answers while anything moves: every daemon line and
/// every provider request or stream change counts as progress, and
/// [`STALL`] without any is a stalled turn.
fn settle_until<T>(
    client: &WireClient,
    mock: &MockLlm,
    what: &str,
    done: impl Fn() -> Option<T>,
) -> T {
    let mut seen = (client.len(), mock.changes());
    let mut last_progress = Instant::now();
    loop {
        if let Some(done) = done() {
            return done;
        }
        let now = (client.len(), mock.changes());
        if now != seen {
            seen = now;
            last_progress = Instant::now();
        }
        assert!(
            last_progress.elapsed() < STALL,
            "{what} stalled: nothing moved for {STALL:?}; provider log tail: {:#?}",
            mock_llm::summary(&mock.log())
                .into_iter()
                .rev()
                .take(10)
                .collect::<Vec<_>>()
        );
        // The wait itself: woken by the next daemon line or within 50 ms.
        client.wait_beyond(seen.0, Duration::from_millis(50));
    }
}

#[test]
fn compaction_soak_300_turns() {
    let started = Instant::now();
    let dir = tempfile::tempdir().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let calibration_dir = agent_dir.join("calibration");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&calibration_dir).expect("calibration dir");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let overflowed = Arc::new(AtomicBool::new(false));
    let script_overflowed = Arc::clone(&overflowed);
    let mock = MockLlm::start(move |request| script(request, &script_overflowed));
    let settings = json!({
        "defaultProvider": "mock",
        "defaultModel": MODEL,
        "compaction": {
            "enabled": true,
            "reserveTokens": RESERVE,
            "keepRecentTokens": KEEP_RECENT,
        },
    });
    std::fs::write(agent_dir.join("settings.json"), settings.to_string()).expect("settings");
    std::fs::write(
        agent_dir.join("models.json"),
        mock.models_json(MODEL, 128_000, 2_048).to_string(),
    )
    .expect("models.json");
    let socket = dir.path().join("daemon.sock");
    let _supervisor = Supervisor::start(&socket, &agent_dir, &dir.path().join("supervisor.log"));
    let mut client = WireClient::connect(&socket);
    let create = |client: &mut WireClient, sessions: &std::path::Path| {
        let created = client.request(
            &json!({ "type": "create", "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": sessions.to_string_lossy(),
                "provider": "mock",
                "model": MODEL,
                // A chat-memory root starts every turn from the view and
                // never threshold-compacts; a depth-1 session keeps its
                // whole context.
                "rlmDepth": 1,
            }}),
            Duration::from_mins(3),
        );
        assert_eq!(created["success"], true, "create: {created}");
        let session_id = created["data"]["activeSessionId"]
            .as_str()
            .expect("session id")
            .to_string();
        let attached = client.request(
            &json!({ "type": "attach", "activeSessionId": session_id }),
            Duration::from_mins(3),
        );
        assert_eq!(attached["success"], true, "attach: {attached}");
        session_id
    };

    // Calibration: one turn on a throwaway session measures the fixed
    // request overhead, so the window is small relative to it whatever the
    // system prompt and tool schemas weigh.
    let calibration = create(&mut client, &calibration_dir);
    let id = client.send(&json!({
        "type": "prompt_and_wait", "activeSessionId": calibration, "message": "calibrate",
    }));
    let done = settle(&client, &mock, &id, "the calibration turn");
    assert_eq!(done["success"], true, "calibration: {done}");
    let overhead = mock.log()[0].request.prompt_tokens;
    let window = overhead + ROOM;
    std::fs::write(
        agent_dir.join("models.json"),
        mock.models_json(MODEL, window, 2_048).to_string(),
    )
    .expect("models.json");
    mock.set_window(window);
    let calibration_requests = mock.log().len();

    let session_id = create(&mut client, &session_dir);
    let events_from = client.len();
    let mut prompts: Vec<String> = Vec::new();
    for turn in 1..=TURNS {
        let name = format!("s{turn}");
        if turn % 23 == 0 {
            // Busy: the answer holds on its gate; a steer and a follow-up
            // arrive while the run streams, then the gate opens.
            let message = padded(&name, &[BUSY]);
            let id = client.send(&json!({
                "type": "prompt", "activeSessionId": session_id, "message": message,
            }));
            let response = settle(&client, &mock, &id, &format!("turn {turn}'s admission"));
            assert_eq!(response["success"], true, "busy prompt: {response}");
            mock.wait_for(
                Duration::from_mins(3),
                "the busy turn's held answer",
                |log| {
                    log.iter()
                        .any(|entry| {
                            entry.holding && entry.request.prompt.starts_with(&format!("{name} "))
                        })
                        .then_some(())
                },
            );
            let steer = format!("steer{turn} change course");
            let follow = format!("follow{turn} then this");
            for (kind, text) in [("steer", &steer), ("follow_up", &follow)] {
                let id = client.send(&json!({
                    "type": kind, "activeSessionId": session_id, "message": text,
                }));
                let response = settle(&client, &mock, &id, &format!("turn {turn}'s {kind}"));
                assert_eq!(response["success"], true, "{kind}: {response}");
            }
            mock.open_gate(&name);
            let id = client.send(&json!({
                "type": "wait_for_idle", "activeSessionId": session_id,
            }));
            let idle = settle(&client, &mock, &id, &format!("turn {turn}'s idle"));
            assert_eq!(idle["success"], true, "idle: {idle}");
            prompts.extend([message, steer, follow]);
            continue;
        }
        // From the middle on, turns carry the overflow tag until one
        // request takes the injected overflow.
        let marks: &[&str] = if turn >= TURNS / 2 && !overflowed.load(Ordering::SeqCst) {
            &[OVERFLOW]
        } else if turn % 7 == 0 {
            &[TOOL]
        } else {
            &[]
        };
        let message = padded(&name, marks);
        let id = client.send(&json!({
            "type": "prompt_and_wait", "activeSessionId": session_id, "message": message,
        }));
        let done = settle(&client, &mock, &id, &format!("turn {turn}"));
        assert_eq!(done["success"], true, "turn {turn}: {done}");
        prompts.push(message);
    }
    let id = client.send(&json!({ "type": "wait_for_idle", "activeSessionId": session_id }));
    let idle = settle(&client, &mock, &id, "the final idle");
    assert_eq!(idle["success"], true, "idle: {idle}");
    // An early compaction is a background task beside the turn that
    // started it, outside the idle above: the verdict waits until every
    // compaction that started has ended.
    settle_until(&client, &mock, "the last compaction", || {
        let events = client.events_from(events_from);
        let count = |kind: &str| events.iter().filter(|event| event["type"] == kind).count();
        (count("compaction_start") == count("compaction_end")).then_some(())
    });

    // The provider's verdict: one overflow (the injected one), nothing
    // else over the window, no dropped stream.
    let log = mock.log();
    let soak = &log[calibration_requests..];
    let overflows: Vec<usize> = soak
        .iter()
        .filter(|entry| entry.served == Served::Overflowed)
        .map(|entry| entry.request.index)
        .collect();
    assert_eq!(
        overflows.len(),
        1,
        "only the injected overflow: {overflows:?}"
    );
    assert!(
        soak.iter()
            .all(|entry| matches!(entry.served, Served::Complete | Served::Overflowed)),
        "every request served whole"
    );

    // The session's verdict, from its events.
    let events = client.events_from(events_from);
    let ends: Vec<&Value> = events
        .iter()
        .filter(|event| event["type"] == "compaction_end")
        .collect();
    let failed: Vec<&&Value> = ends
        .iter()
        .filter(|event| {
            event["aborted"] == true || event.get("errorMessage").is_some_and(|e| !e.is_null())
        })
        .collect();
    assert!(failed.is_empty(), "failed compactions: {failed:#?}");
    let mut reasons: BTreeMap<String, usize> = BTreeMap::new();
    for end in &ends {
        *reasons
            .entry(end["reason"].as_str().unwrap_or("?").to_string())
            .or_default() += 1;
    }

    // The durable verdict.
    let dirs = durable_store::session_dirs(&session_dir);
    assert_eq!(dirs.len(), 1, "one soak session: {dirs:?}");
    let transcript = durable_store::read_transcript(&dirs[0]);
    let ids: Vec<u64> = transcript
        .entries
        .iter()
        .map(|entry| entry["id"].as_u64().expect("entry id"))
        .collect();
    assert!(
        ids.windows(2).all(|pair| pair[0] < pair[1]),
        "transcript ids are monotonic"
    );
    let compactions = transcript.of_kind("pi.compaction");
    let outcome_rows = transcript.custom_rows("compaction_outcome");
    assert!(outcome_rows.is_empty(), "failure rows: {outcome_rows:#?}");
    assert_eq!(
        compactions.len(),
        ends.len(),
        "every compaction_end committed one entry: {reasons:?}"
    );
    assert!(
        compactions.len() > 20,
        "the threshold crossed only {} times: {reasons:?}",
        compactions.len()
    );
    assert!(
        compactions
            .iter()
            .any(|entry| entry["data"]["reason"] == "overflow"),
        "the overflow recovered by compacting: {reasons:?}"
    );
    let users: Vec<String> = transcript
        .of_kind("pi.user")
        .iter()
        .flat_map(|entry| entry["model"].as_array().cloned().unwrap_or_default())
        .flat_map(|message| match &message["content"] {
            Value::String(text) => vec![text.clone()],
            Value::Array(blocks) => blocks
                .iter()
                .filter_map(|block| block["text"].as_str().map(str::to_string))
                .collect(),
            _ => Vec::new(),
        })
        .collect();
    assert_same_items(&users, &prompts, "every prompt stored exactly once");
    let first_out_of_order = users
        .iter()
        .zip(&prompts)
        .position(|(user, prompt)| user != prompt);
    assert_eq!(first_out_of_order, None, "prompts stored in send order");
    let answers: Vec<String> = transcript
        .of_kind("pi.assistant")
        .iter()
        .flat_map(|entry| entry["model"].as_array().cloned().unwrap_or_default())
        .flat_map(|message| match &message["content"] {
            Value::Array(blocks) => blocks
                .iter()
                .filter_map(|block| block["text"].as_str().map(str::to_string))
                .filter(|text| text.starts_with("answer to "))
                .collect(),
            _ => Vec::new(),
        })
        .collect();
    // A steer queued while the run streams its last answer lands at the
    // run's final boundary together with the queued follow-up (spec §6:
    // the final boundary places steers and follow-ups), so one answer
    // addresses both: the follow-up's.
    let expected_answers: Vec<String> = prompts
        .iter()
        .filter(|prompt| !prompt.starts_with("steer"))
        .map(|prompt| answer_for(prompt))
        .collect();
    assert_same_items(&answers, &expected_answers, "every prompt answered once");
    eprintln!(
        "soak: {} prompts, {} compactions {reasons:?}, {} provider requests, overhead {overhead} tokens, window {window}, {:?}",
        prompts.len(),
        compactions.len(),
        soak.len(),
        started.elapsed()
    );
}

/// `actual` and `expected` hold the same items, each as often; the failure
/// names what is missing and what is extra.
fn assert_same_items(actual: &[String], expected: &[String], what: &str) {
    let mut counts: BTreeMap<&str, i64> = BTreeMap::new();
    for item in actual {
        *counts.entry(item).or_default() += 1;
    }
    for item in expected {
        *counts.entry(item).or_default() -= 1;
    }
    let differences: Vec<(&str, i64)> = counts
        .into_iter()
        .filter(|(_, count)| *count != 0)
        .map(|(item, count)| (item.get(..80).unwrap_or(item), count))
        .collect();
    assert!(
        differences.is_empty(),
        "{what}: (item, extra count; negative = missing) {differences:#?}"
    );
}
