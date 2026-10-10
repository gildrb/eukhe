//! Range selection and serialization (`test/harness-compaction.test.ts`,
//! "range selection" and "serialization").

use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_thinking, faux_tool_call, FauxAssistantMessageOptions,
};
use eukhe_types::pi_ai::{
    AssistantMessage, IndexMap, JsonObject as PiJsonObject, Message, StopReason, SystemContent,
    SystemMessage, TextContent, ToolResultMessage, UserContent, UserContentBlock, UserMessage,
};

use super::{select_cut, serialize_conversation};
use crate::harness::context::order_tool_results;
use crate::harness::types::ContextView;
use crate::types::{ConversationId, EntryId, EntryRecord};

/// Text of about `tokens` estimated tokens, starting with `label`.
pub(crate) fn text(label: &str, tokens: usize) -> String {
    let fill = (tokens * 4).saturating_sub(label.len() + 1);
    format!("{label} {}", "x".repeat(fill))
}

/// Entry IDs in creation order (TS `nextId`).
struct Ids(u64);

impl Ids {
    fn entry(&mut self, kind: &str, model: Vec<Message>, head: Option<u64>) -> EntryRecord {
        self.0 += 1;
        EntryRecord {
            model: Some(model),
            data: None,
            edits: None,
            kind: kind.to_owned(),
            id: EntryId::from_number(self.0),
            conversation_id: ConversationId::from_number(1),
            head: head.map(EntryId::from_number),
            by_task_id: None,
        }
    }
}

fn user(content: impl Into<String>) -> Message {
    Message::User(UserMessage {
        content: UserContent::Text(content.into()),
        timestamp: 0,
    })
}

fn assistant(content: &str, calls: &[&str], stop_reason: StopReason) -> Message {
    let mut blocks = vec![faux_text(content)];
    blocks.extend(
        calls
            .iter()
            .map(|id| faux_tool_call("read", PiJsonObject::new(), Some((*id).to_owned()))),
    );
    let message: AssistantMessage = AssistantMessage {
        stop_reason,
        ..faux_assistant_message(blocks, FauxAssistantMessageOptions::default())
    };
    Message::Assistant(message)
}

fn answer(content: &str) -> Message {
    assistant(content, &[], StopReason::Stop)
}

fn calling(content: &str, calls: &[&str]) -> Message {
    assistant(content, calls, StopReason::Stop)
}

fn tool_result(call_id: &str, content: impl Into<String>) -> Message {
    Message::ToolResult(ToolResultMessage {
        tool_call_id: call_id.to_owned(),
        tool_name: "read".to_owned(),
        content: vec![UserContentBlock::Text(TextContent::new(content))],
        details: None,
        usage: None,
        nested_calls: None,
        is_error: false,
        timestamp: 0,
        duration_ms: None,
    })
}

fn system_sections(section: String) -> Message {
    let mut sections = IndexMap::new();
    sections.insert("s".to_owned(), Some(section));
    Message::System(SystemMessage {
        content: SystemContent::Text(String::new()),
        sections: Some(sections),
        tools_added: None,
        tools_removed: None,
        timestamp: 0,
    })
}

fn is_excluded(message: &Message) -> bool {
    matches!(
        message,
        Message::Assistant(assistant)
            if matches!(assistant.stop_reason, StopReason::Error | StopReason::Aborted | StopReason::Deferred)
    )
}

/// A view over `entries` whose contributions are their models, with excluded
/// assistants removed.
fn view(entries: Vec<EntryRecord>, head: Option<EntryRecord>) -> ContextView {
    let all: Vec<EntryRecord> = head.iter().cloned().chain(entries).collect();
    let contributions: Vec<Vec<Message>> = all
        .iter()
        .map(|record| {
            record
                .model
                .iter()
                .flatten()
                .filter(|message| !is_excluded(message))
                .cloned()
                .collect()
        })
        .collect();
    let flat: Vec<Message> = contributions.iter().flatten().cloned().collect();
    ContextView {
        head,
        entries: all,
        messages: order_tool_results(&flat),
        contributions,
    }
}

#[test]
fn keeps_about_keep_recent_tokens_and_cuts_at_the_first_candidate_at_or_after_the_budget() {
    let mut ids = Ids(0);
    let entries = vec![
        ids.entry("pi.user", vec![user(text("1", 10))], None),
        ids.entry("pi.assistant", vec![calling("2", &["c1"])], None),
        ids.entry(
            "pi.tool-result",
            vec![tool_result("c1", text("3", 3000))],
            None,
        ),
        ids.entry("pi.assistant", vec![answer(&text("4", 10))], None),
        ids.entry("pi.user", vec![user(text("5", 10))], None),
        ids.entry("pi.assistant", vec![answer(&text("6", 10))], None),
    ];
    assert_eq!(select_cut(&view(entries, None), 2000.0), Some(3));
}

#[test]
fn cuts_at_a_user_entry() {
    let mut ids = Ids(0);
    let entries = vec![
        ids.entry("pi.user", vec![user(text("u1", 100))], None),
        ids.entry("pi.assistant", vec![answer(&text("a1", 100))], None),
        ids.entry("pi.user", vec![user(text("u2", 100))], None),
        ids.entry("pi.assistant", vec![answer(&text("a2", 100))], None),
    ];
    assert_eq!(select_cut(&view(entries, None), 150.0), Some(2));
}

#[test]
fn cuts_at_an_assistant_in_the_middle_of_one_long_run_and_never_at_a_tool_result() {
    let mut ids = Ids(0);
    let mut entries = vec![ids.entry("pi.user", vec![user("do it")], None)];
    for index in 0..5 {
        let call = format!("c{index}");
        entries.push(ids.entry(
            "pi.assistant",
            vec![calling(&format!("step {index}"), &[call.as_str()])],
            None,
        ));
        entries.push(ids.entry(
            "pi.tool-result",
            vec![tool_result(&call, text(&format!("r{index}"), 100))],
            None,
        ));
    }
    let cut = select_cut(&view(entries.clone(), None), 150.0).expect("a cut");
    // The budget is reached at the fourth result; the cut is the last call,
    // whose result it keeps.
    assert_eq!(entries[cut].kind, "pi.assistant");
    assert_eq!(cut, 9);
}

#[test]
fn keeps_a_huge_last_tool_result_together_with_its_assistant() {
    let mut ids = Ids(0);
    let entries = vec![
        ids.entry("pi.user", vec![user("u")], None),
        ids.entry("pi.assistant", vec![calling("a", &["c"])], None),
        ids.entry(
            "pi.tool-result",
            vec![tool_result("c", text("big", 5000))],
            None,
        ),
    ];
    assert_eq!(select_cut(&view(entries, None), 100.0), Some(1));
}

#[test]
fn never_cuts_at_a_system_entry_or_an_excluded_error_or_aborted_answer() {
    let mut ids = Ids(0);
    let entries = vec![
        ids.entry("pi.user", vec![user(text("u1", 100))], None),
        ids.entry("pi.assistant", vec![answer(&text("a1", 100))], None),
        ids.entry("pi.system", vec![system_sections(text("s", 100))], None),
        ids.entry(
            "pi.assistant",
            vec![assistant(&text("err", 100), &[], StopReason::Error)],
            None,
        ),
        ids.entry(
            "pi.assistant",
            vec![assistant(&text("stopped", 100), &[], StopReason::Aborted)],
            None,
        ),
        ids.entry("pi.assistant", vec![answer(&text("a2", 100))], None),
    ];
    // The walk reaches 150 at the system entry; the excluded answers after it
    // contribute nothing.
    assert_eq!(select_cut(&view(entries, None), 150.0), Some(5));
}

#[test]
fn follows_edited_contributions_an_omitted_entry_adds_nothing_and_is_no_candidate() {
    let mut ids = Ids(0);
    let entries = vec![
        ids.entry("pi.user", vec![user(text("u1", 100))], None),
        ids.entry("pi.assistant", vec![answer(&text("a1", 100))], None),
        ids.entry("pi.user", vec![user(text("u2", 100))], None),
        ids.entry("pi.assistant", vec![answer(&text("a2", 100))], None),
    ];
    let plain = view(entries, None);
    assert_eq!(select_cut(&plain, 150.0), Some(2));
    let contributions: Vec<Vec<Message>> = plain
        .contributions
        .iter()
        .enumerate()
        .map(|(index, messages)| {
            if index == 2 {
                Vec::new()
            } else {
                messages.clone()
            }
        })
        .collect();
    let flat: Vec<Message> = contributions.iter().flatten().cloned().collect();
    let omitted = ContextView {
        messages: order_tool_results(&flat),
        contributions,
        ..plain
    };
    assert_eq!(select_cut(&omitted, 150.0), Some(1));
}

#[test]
fn does_not_cut_at_a_user_entry_that_a_result_of_the_preceding_call_still_follows() {
    let mut ids = Ids(0);
    let entries = vec![
        ids.entry("pi.user", vec![user(text("u1", 100))], None),
        ids.entry("pi.assistant", vec![calling("a", &["c"])], None),
        ids.entry("pi.user", vec![user(text("steer", 100))], None),
        ids.entry(
            "pi.tool-result",
            vec![tool_result("c", text("r", 100))],
            None,
        ),
        ids.entry("pi.assistant", vec![answer(&text("a2", 100))], None),
    ];
    // The budget is reached at the steer; its result follows it, so the cut
    // moves to the next assistant.
    assert_eq!(select_cut(&view(entries, None), 250.0), Some(4));
}

#[test]
fn finds_nothing_when_the_budget_is_never_reached_or_only_the_marker_precedes_the_cut() {
    let mut ids = Ids(0);
    let small = vec![
        ids.entry("pi.user", vec![user("hi")], None),
        ids.entry("pi.assistant", vec![answer("hello")], None),
    ];
    assert_eq!(select_cut(&view(small, None), 150.0), None);
    let marker = ids.entry("pi.compaction", vec![user("summary")], Some(0));
    // The budget is reached at the only entry after the marker, so the marker
    // alone would be summarized.
    let only = vec![ids.entry("pi.user", vec![user(text("u", 200))], None)];
    assert_eq!(select_cut(&view(only, Some(marker)), 150.0), None);
}

#[test]
fn summarizes_an_earlier_summary_marker_first() {
    let mut ids = Ids(0);
    let marker = ids.entry("pi.compaction", vec![user("EARLIER")], Some(0));
    let kept = vec![
        ids.entry("pi.user", vec![user(text("u1", 100))], None),
        ids.entry("pi.assistant", vec![answer(&text("a1", 100))], None),
        ids.entry("pi.user", vec![user(text("u2", 100))], None),
        ids.entry("pi.assistant", vec![answer(&text("a2", 100))], None),
    ];
    let selected = view(kept, Some(marker));
    assert_eq!(select_cut(&selected, 150.0), Some(3));
    let prefix: Vec<Message> = selected.contributions[..3]
        .iter()
        .flatten()
        .cloned()
        .collect();
    assert!(serialize_conversation(&prefix).starts_with("[User]: EARLIER"));
}

#[test]
fn writes_a_transcript_truncates_tool_results_and_omits_system_messages() {
    let mut arguments = PiJsonObject::new();
    arguments.insert("path".to_owned(), "a.ts".into());
    let call = faux_tool_call("read", arguments, Some("c".to_owned()));
    let messages = vec![
        system_sections("hidden".to_owned()),
        user("hello"),
        Message::Assistant(faux_assistant_message(
            vec![faux_thinking("hmm"), faux_text("sure"), call],
            FauxAssistantMessageOptions::default(),
        )),
        tool_result("c", "y".repeat(2500)),
    ];
    let serialized = serialize_conversation(&messages);
    assert!(!serialized.contains("hidden"));
    assert!(serialized.contains("[User]: hello"));
    assert!(serialized.contains("[Assistant thinking]: hmm"));
    assert!(serialized.contains("[Assistant]: sure"));
    assert!(serialized.contains(r#"[Assistant tool calls]: read(path="a.ts")"#));
    assert!(serialized.contains(&format!(
        "[Tool result]: {}\n\n[... 500 more characters truncated]",
        "y".repeat(2000)
    )));
}

/// Not in the TS suite: the persisted checkpoint has the TS key order
/// (`{ phase, ...request }` and `{ phase, ...request, until }`).
#[test]
fn serializes_checkpoints_like_the_ts_object_literals() {
    use eukhe_chord::json::{from_json, to_json};
    use eukhe_types::pi_ai::ModelThinkingLevel;

    use super::{CompactionCheckpoint, RetryRequest, SummaryRequest};
    use crate::harness::types::{ConversationStreamOptions, ModelRef};

    let request = SummaryRequest {
        attempt: 1,
        model: ModelRef {
            provider: "faux".to_owned(),
            model_id: "faux-1".to_owned(),
        },
        thinking_level: ModelThinkingLevel::Off,
        stream_options: ConversationStreamOptions::default(),
        max_tokens: 800.0,
        tail: EntryId::from_number(7),
        first_kept: EntryId::from_number(5),
    };
    let cases = [
        (CompactionCheckpoint::Select, r#"{"phase":"select"}"#),
        (
            CompactionCheckpoint::Summarize(request.clone()),
            r#"{"phase":"summarize","attempt":1,"model":{"provider":"faux","modelId":"faux-1"},"thinkingLevel":"off","streamOptions":{},"maxTokens":800,"tail":7,"firstKept":5}"#,
        ),
        (
            CompactionCheckpoint::Retry(RetryRequest {
                request,
                until: 1234.5,
            }),
            r#"{"phase":"retry","attempt":1,"model":{"provider":"faux","modelId":"faux-1"},"thinkingLevel":"off","streamOptions":{},"maxTokens":800,"tail":7,"firstKept":5,"until":1234.5}"#,
        ),
    ];
    for (checkpoint, json) in cases {
        let value = to_json(&checkpoint).unwrap();
        assert_eq!(value.to_string(), json);
        assert_eq!(
            from_json::<CompactionCheckpoint>(&value).unwrap(),
            checkpoint
        );
    }
}
