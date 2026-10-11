//! Port of `system-message-replay.test.ts`.

use serde_json::json;

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, StopReason, TextContent, ToolConstrainedSampling,
    Usage, UserContent, UserMessage,
};

use super::*;
use crate::utils::text::{get_system_message_text, render_system_message_update};

fn tool(name: &str) -> Tool {
    tool_described(name, &format!("{name} tool"))
}

fn tool_described(name: &str, description: &str) -> Tool {
    Tool {
        name: name.to_owned(),
        description: description.to_owned(),
        parameters: json!({ "type": "object", "properties": {} }).into(),
        constrained_sampling: None,
    }
}

// Builds the `SystemMessage::sections` field value, which is optional.
#[allow(clippy::unnecessary_wraps)]
fn sections(entries: &[(&str, Option<&str>)]) -> Option<IndexMap<String, Option<String>>> {
    Some(
        entries
            .iter()
            .map(|(name, value)| ((*name).to_owned(), value.map(str::to_owned)))
            .collect(),
    )
}

fn system(content: &str, timestamp: u64) -> SystemMessage {
    SystemMessage {
        content: SystemContent::Text(content.to_owned()),
        sections: None,
        tools_added: None,
        tools_removed: None,
        timestamp,
    }
}

fn user(content: &str, timestamp: u64) -> Message {
    Message::User(UserMessage {
        content: UserContent::Text(content.to_owned()),
        timestamp,
    })
}

fn assistant(text: &str, timestamp: u64) -> Message {
    Message::Assistant(AssistantMessage {
        content: vec![AssistantContentBlock::Text(TextContent::new(text))],
        api: "faux".into(),
        provider: "faux".into(),
        model: "faux-1".into(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: StopReason::Stop,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp,
        duration_ms: None,
    })
}

fn transcript() -> TranscriptContext {
    normalize_context(Context {
        system_prompt: None,
        messages: vec![
            Message::System(SystemMessage {
                sections: sections(&[("a", Some("<a>1</a>")), ("b", Some("<b>1</b>"))]),
                tools_added: Some(vec![tool("first")]),
                ..system("base", 10)
            }),
            user("hello", 11),
            Message::System(system("also do this", 12)),
            assistant("ok", 13),
            Message::System(SystemMessage {
                sections: sections(&[
                    ("a", Some("<a>2</a>")),
                    ("b", None),
                    ("c", Some("<c>1</c>")),
                ]),
                tools_removed: Some(vec![ToolReference {
                    name: "first".into(),
                }]),
                tools_added: Some(vec![tool("second")]),
                ..system("", 14)
            }),
        ],
        tools: None,
    })
}

#[test]
fn replays_content_sections_and_tools_into_one_leading_message() {
    let transcript = transcript();
    assert_eq!(
        get_current_system_message(transcript.messages()),
        Some(SystemMessage {
            sections: sections(&[("a", Some("<a>2</a>")), ("c", Some("<c>1</c>"))]),
            tools_added: Some(vec![tool("second")]),
            ..system("base\n\nalso do this", 10)
        })
    );
    assert_eq!(
        get_current_system_prompt(transcript.messages()),
        "base\n\nalso do this\n\n<a>2</a>\n\n<c>1</c>"
    );
}

#[test]
fn collapse_keeps_only_non_system_messages_after_the_replayed_head() {
    let collapsed = collapse_system_messages(transcript());
    assert_eq!(
        collapsed
            .messages()
            .iter()
            .map(Message::role)
            .collect::<Vec<_>>(),
        ["system", "user", "assistant"]
    );
    assert_eq!(collapse_system_messages(collapsed.clone()), collapsed);
}

#[test]
fn replay_of_a_transcript_without_system_messages_is_empty() {
    let context = normalize_context(Context {
        system_prompt: None,
        messages: vec![user("hi", 1)],
        tools: None,
    });
    assert_eq!(get_current_system_message(context.messages()), None);
    assert_eq!(get_current_system_prompt(context.messages()), "");
    assert_eq!(
        collapse_system_messages(context.clone()).messages(),
        context.messages()
    );
}

#[test]
fn a_late_full_patch_on_a_transcript_without_a_leading_message_replays_as_the_prompt() {
    let context = normalize_context(Context {
        system_prompt: None,
        messages: vec![
            user("old session", 1),
            Message::System(SystemMessage {
                sections: sections(&[("preamble", Some("You are pi."))]),
                tools_added: Some(vec![tool("x")]),
                ..system("", 2)
            }),
        ],
        tools: None,
    });
    assert_eq!(get_current_system_prompt(context.messages()), "You are pi.");
    let collapsed = collapse_system_messages(context);
    let head = collapsed.messages()[0].as_system().unwrap();
    assert_eq!(head.tools_added, Some(vec![tool("x")]));
}

#[test]
fn renders_complete_prompts_and_framed_updates() {
    let transcript = transcript();
    let leading = transcript.messages()[0].as_system().unwrap();
    let update = transcript.messages()[4].as_system().unwrap();
    assert_eq!(
        get_system_message_text(leading),
        "base\n\n<a>1</a>\n\n<b>1</b>"
    );
    assert_eq!(
        render_system_message_update(update),
        [
            "Updated system prompt section \"a\":\n\n<a>2</a>",
            "Removed system prompt section \"b\".",
            "Updated system prompt section \"c\":\n\n<c>1</c>",
        ]
        .join("\n\n")
    );
}

#[test]
fn normalizes_the_legacy_prompt_and_tool_fields_into_a_leading_system_message() {
    let messages = vec![user("hi", 1)];
    let plain = |system_prompt: Option<&str>, tools: Option<Vec<Tool>>| {
        normalize_context(Context {
            system_prompt: system_prompt.map(str::to_owned),
            messages: messages.clone(),
            tools,
        })
    };
    assert_eq!(plain(None, None).messages(), messages.as_slice());
    assert_eq!(
        plain(Some(""), Some(Vec::new())).messages(),
        messages.as_slice()
    );
    let mut expected = vec![Message::System(SystemMessage {
        tools_added: Some(vec![tool("a")]),
        ..system("be brief", 0)
    })];
    expected.extend(messages.clone());
    assert_eq!(
        plain(Some("be brief"), Some(vec![tool("a")])).messages(),
        expected.as_slice()
    );
}

#[test]
fn compares_tool_declarations_without_executable_or_undefined_fields() {
    // Rust tools carry no executable or `undefined` fields; the declaration is the value.
    assert!(declarations_equal(&tool("a"), &tool("a")));
    assert!(!declarations_equal(
        &tool("a"),
        &tool_described("a", "changed")
    ));
    let disabled = Tool {
        constrained_sampling: Some(ToolConstrainedSampling::Disabled),
        ..tool("a")
    };
    assert!(!declarations_equal(&tool("a"), &disabled));
    let reordered = Tool {
        parameters: json!({ "properties": {}, "type": "object" }).into(),
        ..tool("a")
    };
    assert!(!declarations_equal(&tool("a"), &reordered));
}

#[test]
fn tool_state_changes_treat_changed_definitions_as_removal_plus_addition() {
    let changes = get_tool_state_changes(
        &[tool("a"), tool("b")],
        &[tool_described("b", "changed"), tool("c")],
    );
    assert_eq!(
        changes,
        ToolStateChanges {
            tools_added: vec![tool_described("b", "changed"), tool("c")],
            tools_removed: vec![
                ToolReference { name: "a".into() },
                ToolReference { name: "b".into() }
            ],
        }
    );
    assert_eq!(
        get_tool_state_changes(&[tool("a")], &[tool("a")]),
        ToolStateChanges {
            tools_added: Vec::new(),
            tools_removed: Vec::new(),
        }
    );
}

#[test]
// `hasToolRedefinitions` is deprecated in TS too; its test still runs there.
#[allow(deprecated)]
fn detects_non_additive_tool_history_and_redefinitions() {
    let transcript = transcript();
    assert!(has_non_additive_tool_changes(transcript.messages()));
    assert!(!has_tool_redefinitions(transcript.messages()));
    let additions = |second: Tool| {
        normalize_context(Context {
            system_prompt: None,
            messages: vec![
                Message::System(SystemMessage {
                    tools_added: Some(vec![tool("a")]),
                    ..system("", 1)
                }),
                Message::System(SystemMessage {
                    tools_added: Some(vec![second]),
                    ..system("", 2)
                }),
            ],
            tools: None,
        })
    };
    let additive = additions(tool("b"));
    assert!(!has_non_additive_tool_changes(additive.messages()));
    let redeclared = additions(tool_described("a", "changed"));
    assert!(has_non_additive_tool_changes(redeclared.messages()));
    assert!(has_tool_redefinitions(redeclared.messages()));
}

#[test]
fn resolves_request_tools_for_anchoring_and_full_state_transports() {
    let transcript = transcript();
    let full =
        resolve_transcript_tools(transcript.messages(), /*supports_tool_additions*/ true);
    assert_eq!(
        full,
        TranscriptTools {
            request_tools: vec![tool("second")],
            anchors_additions: false,
        }
    );
    let additive = normalize_context(Context {
        system_prompt: Some("base".into()),
        messages: vec![Message::System(SystemMessage {
            tools_added: Some(vec![tool("late")]),
            ..system("", 2)
        })],
        tools: Some(vec![tool("early")]),
    });
    assert_eq!(
        resolve_transcript_tools(additive.messages(), /*supports_tool_additions*/ true),
        TranscriptTools {
            request_tools: vec![tool("early")],
            anchors_additions: true,
        }
    );
    assert_eq!(
        resolve_transcript_tools(additive.messages(), /*supports_tool_additions*/ false)
            .request_tools,
        vec![tool("early"), tool("late")]
    );
    assert_eq!(
        get_declared_tools(additive.messages()),
        vec![tool("early"), tool("late")]
    );
    assert_eq!(without_initial_system_message(additive.messages()).len(), 1);
    assert_eq!(resolve_transcript(additive.clone(), Some(true)), additive);
}
