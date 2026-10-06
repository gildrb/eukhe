use super::frame::indicator_row;
use super::*;
use crate::chat::{AssistantMessage, MessageBlock};
use crate::style::Modifier;
use crate::theme::{ColorMode, Theme, ThemeBg, ThemeColor};
use crate::tool_card::{ToolCallCard, ToolResultView};
use crate::width::str_width;
use crate::Line;

fn view() -> AgentView {
    AgentView::new(Theme::builtin("eukhe", ColorMode::TrueColor))
}

fn view_with(entries: Vec<ChatEntry>) -> AgentView {
    let mut view = AgentView::new(crate::theme::Theme::builtin(
        "eukhe",
        crate::theme::ColorMode::Color256,
    ));
    for entry in entries {
        view.push_entry(entry);
    }
    view
}

fn settled_tool_card(id: &str) -> ChatEntry {
    ChatEntry::Tool(Box::new(ToolCallCard {
        id: id.to_string(),
        name: "bash".to_string(),
        args: serde_json::json!({"command": "echo done"}),
        started: true,
        started_at: Some(std::time::Instant::now()),
        ended_at: Some(std::time::Instant::now()),
        result: Some(ToolResultView {
            content: vec![serde_json::json!({"type": "text", "text": "done"})],
            details: serde_json::Value::Null,
            is_error: false,
        }),
        result_partial: false,
        aborted: false,
    }))
}

fn transcript_text(view: &mut AgentView, width: usize) -> String {
    let rows = view.render_transcript(width);
    rows.iter()
        .map(|line| line.iter().map(|span| span.content.as_str()).collect())
        .collect::<Vec<String>>()
        .join("\n")
}

fn row_text(line: &Line) -> String {
    line.iter().map(|s| s.content.as_str()).collect::<String>()
}

/// One composed frame as rows: the history it commits, then the live
/// area (a fresh view's first frame carries the whole transcript).
fn composed_rows(v: &mut AgentView, width: usize, height: usize) -> Vec<Line> {
    let composed = v.compose(width, height);
    composed.history.into_iter().chain(composed.live).collect()
}

/// The hardware caret never sits over the factory page: the page is an
/// input-less replacement view, so the frame carries no caret while it
/// is open, and the editor's caret returns once it closes.
#[test]
fn the_factory_page_suppresses_the_stale_editor_cursor() {
    let mut v = view();
    v.factory_view = Some(crate::factory_view::FactoryView::from_reply(
        &serde_json::json!({ "runs": [] }),
        12,
    ));
    assert_eq!(
        v.compose(80, 24).cursor,
        None,
        "the open factory page is an input-less overlay"
    );
    v.factory_view = None;
    assert!(v.compose(80, 24).cursor.is_some());
}

/// A paste never reaches the editor behind an overlay (the key
/// dispatch's frame owners): the input-bearing pickers take it, the
/// input-less overlays consume it, and only the bare dock's editor
/// sees it.
#[test]
fn a_paste_never_reaches_the_editor_behind_an_overlay() {
    let editor_text = |view: &AgentView| view.editor.get_lines().join("\n");
    // The /effort picker takes it into its search.
    let mut v = view();
    v.effort_picker = Some(crate::effort_picker::EffortPicker::new(
        &["high".to_string()],
        None,
    ));
    assert!(v.route_paste("effort"));
    assert_eq!(editor_text(&v), "");
    // The /login provider selector takes it into its search.
    let mut v = view();
    v.provider_auth = Some(crate::provider_auth::ProviderAuthSelector::new(
        crate::provider_auth::AuthSelectorKind::Login,
        Vec::new(),
    ));
    assert!(v.route_paste("login"));
    assert_eq!(editor_text(&v), "");
    // The settings menu takes it into its search.
    let mut v = view();
    v.settings_menu = Some(crate::settings_menu::SettingsMenu::new(Vec::new()));
    assert!(v.route_paste("setting"));
    assert_eq!(editor_text(&v), "");
    // The input-less overlays consume it (the reload box stands in for
    // the whole consume set).
    let mut v = view();
    v.reload_box = Some("reloading".to_string());
    assert!(v.route_paste("never"));
    assert_eq!(editor_text(&v), "");
    // The bare dock: the editor takes it.
    let mut v = view();
    assert!(!v.route_paste("direct"));
    v.editor.handle_paste("direct");
    assert_eq!(editor_text(&v), "direct");
}

fn text_of(line: &Line) -> String {
    line.iter().map(|s| s.content.as_str()).collect::<String>()
}

/// A rendered hint row carries the platform's alt label: the queue
/// browse header quotes `app.message.navigateOlder` and friends through
/// the shared `format_key_text`, so the row shows `Alt+up` on
/// Linux hosts and `Option+up` on macOS (TS
/// `formatKeyPart`'s darwin branch).
/// A fresh chat starts at the collapsed conversation-detail level
/// (operator directive 2026-09-28): the collapse mode renders every
/// activity item exactly as `details` does, with only the thinking
/// blocks hidden - so thinking is hidden BY DEFAULT, and the
/// Ctrl+O cycle from there is unchanged (overview -> details ->
/// all -> overview; the first press reveals the thinking).
#[test]
fn a_chat_starts_at_the_collapsed_detail_level() {
    let mut v = view();
    assert_eq!(v.detail, Detail::Overview, "the startup level is overview");
    assert!(!v.detail.show_thinking());
    assert!(!v.detail.tool_output_expanded());
    assert_eq!(v.detail.next(), Detail::Details);
    v.detail = v.detail.next();
    assert_eq!(v.detail.next(), Detail::All);
    v.detail = v.detail.next();
    assert_eq!(v.detail.next(), Detail::Overview);
}

/// The `!`/`!!` prompt (TS `getBashPromptInfo` + `formatPromptPrefix`):
/// the typed prefix hides behind the styled `! `/`!! ` prompt, later
/// lines keep the prompt column, and the prompt carries the editor
/// border color.
#[test]
fn bang_prompt_renders_in_place_of_the_typed_prefix() {
    let mut v = view();
    v.editor.set_text("!echo hi");
    let frame = v.render_dock(80);
    let joined = frame.iter().map(text_of).collect::<Vec<_>>().join("\n");
    assert!(
        joined.contains("!  echo hi"),
        "the prompt swallows the typed prefix:\n{joined}"
    );
    assert!(
        !joined.contains("> echo hi"),
        "the default prompt does not render for a bang line:\n{joined}"
    );
    let border = v.theme.fg_style(ThemeColor::BorderMuted);
    let prompt_row = frame
        .iter()
        .find(|line| text_of(line).contains("!  echo hi"))
        .expect("the prompt row");
    assert!(
        prompt_row.iter().any(|span| span.style == border),
        "the bang prompt renders through the editor border color"
    );

    let mut v = view();
    v.editor.set_text("!!echo quiet");
    let frame = v.render_dock(80);
    let joined = frame.iter().map(text_of).collect::<Vec<_>>().join("\n");
    assert!(
        joined.contains("!!  echo quiet"),
        "the !! prompt hides its typed prefix:\n{joined}"
    );
}

#[test]
fn autocomplete_dropdown_rows_carry_the_popup_background() {
    // The dropdown floats on the ToolPanelBg overlay above the editor:
    // every span of a menu row (the shared menu_panel rows pad to the
    // full input width with unstyled spans) must carry a background,
    // so an unselected row does not blend into the transcript behind.
    let mut v = view();
    v.editor.handle_input("/");
    v.editor.handle_input("m");
    v.editor.materialize_autocomplete();
    assert!(v.editor.is_showing_autocomplete(), "the dropdown opens");
    let frame = v.render_dock(80);
    let marker_row = frame
        .iter()
        .find(|line| text_of(line).contains('>'))
        .expect("the dropdown renders its marker row");
    assert!(
        marker_row.iter().all(|span| span.style.bg.is_some()),
        "dropdown row spans the popup background: {marker_row:?}"
    );
}

/// The dropdown opens with its top border (the operator's 2026-09-26
/// directive): the panel's first row is the full-width muted `-`
/// rule -- the one every inline menu panel opens with -- drawn on the
/// popup surface directly above the menu rows, so an open slash menu
/// reads as a panel instead of loose transcript rows.
#[test]
fn autocomplete_panel_opens_with_the_top_border_rule() {
    let mut v = view();
    v.editor.handle_input("/");
    v.editor.materialize_autocomplete();
    assert!(v.editor.is_showing_autocomplete(), "the dropdown opens");
    let frame = v.render_dock(80);
    let marker_row = frame
        .iter()
        .position(|line| text_of(line).trim_start().starts_with('>'))
        .expect("the dropdown renders its selected marker row");
    let rule = frame
        .get(marker_row.checked_sub(1).expect("a row above the menu"))
        .expect("the top border row");
    assert_eq!(
        text_of(rule),
        "-".repeat(80),
        "the panel opens with the full-width rule:\n{}",
        frame.iter().map(text_of).collect::<Vec<_>>().join("\n")
    );
    let rule_style = v
        .theme
        .fg_style(ThemeColor::BorderMuted)
        .patch(v.theme.bg_style(ThemeBg::ToolPanelBg));
    assert!(
        rule.iter().all(|span| span.style == rule_style),
        "the rule draws in the muted border color on the popup background: {rule:?}"
    );
}

/// The selected row's wash spans the panel's full width (the
/// operator's 2026-09-26 directive): the leading padding, the menu
/// content, and the trailing padding all carry the soft selection
/// background, so the band reaches both edges like the `/model`
/// picker's selected row, while an unselected row keeps the plain
/// popup background.
#[test]
fn autocomplete_selected_row_washes_the_full_panel_width() {
    let mut v = view();
    v.editor.handle_input("/");
    v.editor.materialize_autocomplete();
    assert!(v.editor.is_showing_autocomplete(), "the dropdown opens");
    let frame = v.render_dock(80);
    let selection_bg = v.theme.soft_selection_style().bg;
    let marker_row = frame
        .iter()
        .position(|line| text_of(line).trim_start().starts_with('>'))
        .expect("the dropdown renders its selected marker row");
    let selected = &frame[marker_row];
    assert_eq!(
        str_width(&text_of(selected)),
        80,
        "the selected row spans the full panel width"
    );
    assert!(
        selected.iter().all(|span| span.style.bg == selection_bg),
        "the selection wash covers every span, both edges included: {selected:?}"
    );
    let unselected = frame
        .get(marker_row + 1)
        .expect("an unselected menu row follows");
    let panel_bg = v.theme.bg_style(ThemeBg::ToolPanelBg).bg;
    assert!(
        unselected.iter().all(|span| span.style.bg == panel_bg),
        "an unselected menu row keeps the popup background: {unselected:?}"
    );
}

#[test]
fn hint_rows_carry_the_platform_alt_label() {
    let mut v = view();
    v.queue_selected = Some(crate::queued::QueueSelectionItem {
        lane: crate::queued::QueueLane::Steering,
        index: 0,
        text: "turn right".to_string(),
        internal: false,
    });
    let frame = composed_rows(&mut v, 80, 24);
    let joined = frame.iter().map(text_of).collect::<Vec<_>>().join("\n");
    assert!(
        joined.contains("browse"),
        "the queue browse header renders: {joined}"
    );
    if std::env::consts::OS == "macos" {
        assert!(joined.contains("Option+up"), "macOS hint row: {joined}");
    } else {
        assert!(joined.contains("Alt+up"), "hint row: {joined}");
    }
}

#[test]
fn compaction_loader_replaces_the_working_loader() {
    // TS `startCompactionLoader`: the compaction loader owns the status
    // area while a compaction runs, working loader hidden.
    let mut v = view();
    v.working = Some(WorkingState {
        activity: "Waiting",
        message: None,
        download: false,
        tokens: 0,
        elapsed_secs: 0,
    });
    v.compaction = Some(crate::chat::CompactionState {
        reason: crate::chat::CompactionReason::Manual,
        custom_instructions: None,
        summary: String::new(),
    });
    let frame = composed_rows(&mut v, 80, 24);
    let flat: Vec<String> = frame.iter().map(row_text).collect();
    assert!(
        flat.iter()
            .any(|l| l.contains("Compacting context... (Ctrl+C to cancel)")),
        "{flat:?}"
    );
    assert!(
        !flat.iter().any(|l| l.contains("Waiting")),
        "the working loader is hidden during compaction: {flat:?}"
    );
    // `compaction_end` clears it; the summary row renders from the
    // transcript entry.
    v.compaction = None;
    v.push_entry(crate::chat::ChatEntry::CompactionSummary {
        summary: "the story so far".to_string(),
        tokens_before: 1234,
        custom_instructions: None,
    });
    let frame = composed_rows(&mut v, 80, 24);
    let flat: Vec<String> = frame.iter().map(row_text).collect();
    assert!(
        flat.iter().any(|l| l.trim() == "* Context compacted"),
        "{flat:?}"
    );
    assert!(
        flat.iter().any(|l| l.trim() == "the story so far"),
        "{flat:?}"
    );
}

/// The live streamed-summary block (the operator's "stream the
/// compacted summary" feature): while a compaction runs, the expanded
/// view (`all` detail) renders the accumulated delta text under the
/// loader row on the branch grammar; collapsed details keep the
/// loader alone; the settling end clears the streamed block when the
/// durable summary row lands.
#[test]
fn compaction_streams_the_summary_under_the_loader_in_expanded_detail() {
    let mut v = view();
    v.detail = crate::chat::Detail::All;
    v.compaction = Some(crate::chat::CompactionState {
        reason: crate::chat::CompactionReason::Threshold,
        custom_instructions: None,
        summary: "The session covered the fleet work.".to_string(),
    });
    let frame = composed_rows(&mut v, 80, 24);
    let flat: Vec<String> = frame.iter().map(row_text).collect();
    let loader = flat
        .iter()
        .position(|l| l.contains("Auto-compacting..."))
        .expect("the loader row renders");
    // The streamed block hangs off the loader row on the branch
    // gutter, the content visible under the spinner.
    let gutter = &flat[loader + 1];
    assert!(
        gutter
            .trim_start()
            .starts_with(crate::branch::BRANCH_GUTTER),
        "the live block nests under the loader: {flat:?}"
    );
    assert!(
        gutter.contains("The session covered the fleet work."),
        "{flat:?}"
    );
    // Collapsed detail (`overview`): the loader stands alone -- no
    // streamed block (TS keeps the loader plain outside `all`).
    v.detail = crate::chat::Detail::Overview;
    let frame = composed_rows(&mut v, 80, 24);
    let flat: Vec<String> = frame.iter().map(row_text).collect();
    assert!(
        flat.iter().any(|l| l.contains("Auto-compacting...")),
        "{flat:?}"
    );
    assert!(
        !flat
            .iter()
            .any(|l| l.contains("The session covered the fleet work.")),
        "no streamed block outside the expanded detail: {flat:?}"
    );
    // `compaction_end` resolves the streamed block into the durable
    // summary row (the loader and the live block clear together).
    v.detail = crate::chat::Detail::All;
    v.compaction = None;
    v.push_entry(crate::chat::ChatEntry::CompactionSummary {
        summary: "The session covered the fleet work.".to_string(),
        tokens_before: 1234,
        custom_instructions: None,
    });
    let frame = composed_rows(&mut v, 80, 24);
    let flat: Vec<String> = frame.iter().map(row_text).collect();
    assert!(
        !flat.iter().any(|l| l.contains("Auto-compacting...")),
        "the loader cleared: {flat:?}"
    );
    assert!(
        flat.iter()
            .any(|l| l.trim() == "* Context compacted - Compacted from 1,234 tokens"),
        "the durable summary row replaced the streamed block: {flat:?}"
    );
}

/// The mode-exit follow recompute (operator directive 2026-09-26):
/// pausing in an expanded mode and collapsing back to `overview`
/// when the collapsed transcript fits the window resumes following --
/// the view already shows the transcript tail, so the follow hint
/// does not render and the tail keeps following new content.
/// The height-exact boundary (the review bots' finding): a window
/// whose bottom lands exactly on the transcript's final chat row --
/// with the empty tail section below it -- is at the bottom, not
/// paused above new content: the follow state re-derives and the
/// hint does not render.
/// The recompute is not a blanket un-pause: a collapse that leaves
/// real rows below the window keeps following paused and the hint
/// rendered (following would actually scroll).
/// The prompt bar's scroll indicators paint on the editor surface's
/// background (operator directive 2026-09-26): the `up N more` row
/// reads as part of the bar, not as text floating on the terminal's
/// bare background.
#[test]
fn the_more_indicator_carry_the_bar_background() {
    let bg = crate::style::Style::default().bg(crate::style::Color::Rgb(10, 11, 12));
    let border = crate::style::Style::default().fg(crate::style::Color::Rgb(1, 2, 3));
    for label in [" ^ 14 more", " v 3 more"] {
        let row = indicator_row(label, bg, border, 20);
        for span in &row {
            assert_eq!(
                span.style.bg,
                Some(crate::style::Color::Rgb(10, 11, 12)),
                "every span of {label:?} carries the bar background"
            );
        }
    }
}

/// The hover affordance (operator directive 2026-09-26): a
/// buttonless motion over a clickable card row brightens that row --
/// Muted spans to the theme's foreground, Dim to Muted -- and only
/// the state change costs a render; a motion across the same row
/// re-styles nothing.
/// The render-side revalidation (the review bots' finding): the
/// hover is a screen coordinate, and the layout moves -- a scroll
/// that brings other content onto the hovered row clears the
/// affordance with the next frame instead of brightening whatever
/// landed there.
/// A settled transcript renders identically from the layout cache and
/// from a fresh layout: caching must never change the frame.
#[test]
fn cached_transcript_rows_match_fresh_render() {
    let mut view = view_with(vec![
        ChatEntry::User {
            text: "hello".to_string(),
        },
        ChatEntry::Assistant(Box::new(AssistantMessage {
            blocks: vec![MessageBlock::Text("world".to_string())],
            has_tool_calls: false,
            streaming: false,
            error: None,
            aborted: false,
        })),
        settled_tool_card("call_1"),
    ]);
    let fresh = transcript_text(&mut view, 80);
    let cached = transcript_text(&mut view, 80);
    assert_eq!(fresh, cached);
}

/// A mutation marked stale re-renders: the cached rows must never hide
/// new content (streamed blocks, tool-card state, attached errors).
#[test]
fn stale_entry_re_renders_new_content() {
    let mut view = view_with(vec![ChatEntry::Assistant(Box::new(AssistantMessage {
        blocks: vec![MessageBlock::Text("part one".to_string())],
        has_tool_calls: false,
        streaming: false,
        error: None,
        aborted: false,
    }))]);
    let before = transcript_text(&mut view, 80);
    if let Some(ChatEntry::Assistant(open)) = view.chat.get_mut(0) {
        open.blocks = vec![MessageBlock::Text("part one part two".to_string())];
    }
    view.mark_entry_stale(0);
    let after = transcript_text(&mut view, 80);
    assert!(before.contains("part one"));
    assert!(!before.contains("part two"));
    assert!(after.contains("part one part two"));
}

/// A settled assistant message keeps no markdown block cache (its
/// rendered rows live once, in the entry layout; the cache exists for
/// the streaming message's per-frame replays), while a streaming
/// message keeps its settled blocks cached for the next frame's
/// replay. The cache-drop must never change the rendered rows.
#[test]
fn settled_messages_render_once_streaming_keeps_block_cache() {
    let settled_rows = {
        let mut view = view_with(vec![ChatEntry::Assistant(Box::new(AssistantMessage {
            blocks: vec![MessageBlock::Text("settled body".to_string())],
            has_tool_calls: false,
            streaming: false,
            error: None,
            aborted: false,
        }))]);
        let text = transcript_text(&mut view, 80);
        assert!(
            view.md_caches.borrow().is_empty(),
            "a settled message keeps no duplicate block-cache copy"
        );
        text
    };
    let mut view = view_with(vec![ChatEntry::Assistant(Box::new(AssistantMessage {
        blocks: vec![MessageBlock::Text("streaming body".to_string())],
        has_tool_calls: false,
        streaming: true,
        error: None,
        aborted: false,
    }))]);
    let streaming_text = transcript_text(&mut view, 80);
    assert!(
        !view.md_caches.borrow().is_empty(),
        "a streaming message keeps its block cache for per-frame replays"
    );
    assert!(
        settled_rows.contains("settled body") && streaming_text.contains("streaming body"),
        "both render their bodies identically through their own paths"
    );
}

/// A running tool card animates: its rows must not be cached (the
/// spinner frame advances), while a settled card's rows ignore the
/// pulse frame.
#[test]
fn running_card_is_not_cached_and_settled_card_is() {
    let running = ChatEntry::Tool(Box::new(ToolCallCard {
        id: "call_r".to_string(),
        name: "bash".to_string(),
        args: serde_json::json!({"command": "sleep 1"}),
        started: true,
        started_at: Some(std::time::Instant::now()),
        ended_at: None,
        result: None,
        result_partial: false,
        aborted: false,
    }));
    let mut view = view_with(vec![running, settled_tool_card("call_d")]);
    view.pulse_frame = 0;
    let frame0 = transcript_text(&mut view, 80);
    view.pulse_frame = 1;
    let frame1 = transcript_text(&mut view, 80);
    assert_ne!(frame0, frame1, "the running spinner must animate");

    // With only a settled card, the pulse frame cannot change rows.
    let mut settled_view = view_with(vec![settled_tool_card("call_d")]);
    settled_view.pulse_frame = 0;
    let s0 = transcript_text(&mut settled_view, 80);
    settled_view.pulse_frame = 7;
    let s7 = transcript_text(&mut settled_view, 80);
    assert_eq!(s0, s7);
}

/// A conversation-detail change re-flows every cached row (thinking
/// blocks and tool output expand).
#[test]
fn detail_change_invalidates_cached_rows() {
    let mut view = view_with(vec![ChatEntry::Assistant(Box::new(AssistantMessage {
        blocks: vec![
            MessageBlock::Thinking("thinking body".to_string()),
            MessageBlock::Text("answer".to_string()),
        ],
        has_tool_calls: false,
        streaming: false,
        error: None,
        aborted: false,
    }))]);
    // The hidden-thinking scenario sits at the collapsed overview
    // level (the startup level since the 2026-09-28 directive).
    view.detail = Detail::Overview;
    let overview = transcript_text(&mut view, 80);
    view.detail = view.detail.next();
    let details = transcript_text(&mut view, 80);
    assert!(!overview.contains("thinking body"));
    assert!(details.contains("thinking body"));
}

/// The compaction summary is a collapsible block (TS
/// `CompactionSummaryMessageComponent`, an `ExpandableEventMessage`):
/// collapsed until the Ctrl+O detail cycle reaches `all`, expanded
/// there, collapsed again when the cycle wraps to `overview`.
#[test]
fn compaction_summary_block_toggles_with_the_detail_cycle() {
    let summary = "## Summary\nthe session story, first line\nand a second line that wraps";
    let mut view = view_with(vec![ChatEntry::CompactionSummary {
        summary: summary.to_string(),
        tokens_before: 12345,
        custom_instructions: Some("the goal".to_string()),
    }]);
    // Collapsed at the collapsed startup level (the overview mode):
    // the header plus the whitespace-collapsed EventSummary, never
    // the token metadata.
    let collapsed = transcript_text(&mut view, 80);
    assert!(collapsed.contains("* Context compacted"));
    assert!(collapsed.contains("## Summary the session story, first line"));
    assert!(!collapsed.contains("Compacted from"));
    // The row is cacheable; the first render stored it. A detail
    // change must re-flow it (the cache drops wholesale), or the
    // block would stay collapsed forever. The cycle's first step
    // is the thinking reveal (`details`): the block stays
    // collapsed there too.
    view.detail = view.detail.next();
    let at_details = transcript_text(&mut view, 80);
    assert_eq!(view.detail, Detail::Details);
    assert!(
        !at_details.contains("Compacted from"),
        "the middle `details` level keeps the block collapsed too: {at_details}"
    );
    view.detail = view.detail.next();
    let expanded = transcript_text(&mut view, 80);
    assert!(
        expanded.contains("Compacted from 12,345 tokens - focus: the goal"),
        "the expanded metadata row renders: {expanded}"
    );
    // The expanded body is markdown, not the EventSummary collapse:
    // the heading renders as its own row.
    assert!(
        expanded.contains("Summary"),
        "the expanded markdown body renders: {expanded}"
    );
    // The cycle wraps through the collapsed startup level: the
    // block collapses again.
    view.detail = view.detail.next();
    let collapsed_again = transcript_text(&mut view, 80);
    assert_eq!(view.detail, Detail::Overview);
    assert!(
        !collapsed_again.contains("Compacted from"),
        "the cycle back to `overview` collapses the block: {collapsed_again}"
    );
}

fn user_row() -> ChatEntry {
    ChatEntry::User {
        text: "hello".to_string(),
    }
}

/// A tool-carrying assistant whose only body is a thinking block: the
/// body hides in collapsed mode (TS `hideThinkingBlock`), so the
/// message's whole height rides the spacing decisions.
fn thinking_tool_assistant() -> ChatEntry {
    ChatEntry::Assistant(Box::new(AssistantMessage {
        blocks: vec![MessageBlock::Thinking("thinking body".to_string())],
        has_tool_calls: true,
        streaming: false,
        error: None,
        aborted: false,
    }))
}

fn agent_message_row() -> ChatEntry {
    ChatEntry::AgentMessage(Box::new(crate::custom_message::AgentMessageRow {
        direction: crate::custom_message::AgentMessageDirection::Received,
        counterpart: "lane".to_string(),
        message: "hi".to_string(),
    }))
}

fn shell_completion_row() -> ChatEntry {
    ChatEntry::ShellCompletion(Box::new(crate::custom_message::ShellCompletionRow {
        pid: Some(1),
        exit_code: Some(0),
        content: "[bash-done]".to_string(),
    }))
}

/// TS `createConversationSpacing.shouldAddLeadingSpace` for one
/// spacing-driven row: scan back over hidden assistant rows, honor the
/// trailing space of a visible assistant, and sit flush against compact
/// TS `UserMessageComponent` is a Box(2,1): its vertical padding row
/// under the content is the first of two blanks before a tool card
/// (the card's `shouldAddLeadingSpace` spacer is the second). The f20
/// spawn frame shows exactly this seam.
#[test]
fn tool_card_after_user_message_keeps_ts_two_blank_seam() {
    let mut view = view_with(vec![
        ChatEntry::User {
            text: "run the cell".to_string(),
        },
        settled_tool_card("t1"),
    ]);
    let rows = view.render_transcript(120);
    let flat: Vec<String> = rows
        .iter()
        .map(|l| l.iter().map(|s| s.content.as_str()).collect())
        .collect();
    let user = flat
        .iter()
        .position(|r| r.contains("run the cell"))
        .expect("user row");
    // The box padding row carries the OSC 133 zone-end markers behind
    // its background spaces; both seam rows are visually empty (zero
    // printable width once the blank padding is trimmed away).
    let empty = |row: &str| crate::width::str_width(row.trim()) == 0;
    assert!(empty(&flat[user + 1]), "box bottom padding row");
    assert!(empty(&flat[user + 2]), "tool leading spacer row");
    assert!(
        flat[user + 3].trim().starts_with("bash"),
        "card after the two blanks: {:?}",
        &flat[user + 3..]
    );
}

/// neighbors (tool cards, agent messages, shell completions).
#[test]
fn conversation_leading_matches_ts_spacing_rules() {
    let visible_assistant = || {
        ChatEntry::Assistant(Box::new(AssistantMessage {
            blocks: vec![MessageBlock::Text("done".to_string())],
            has_tool_calls: true,
            streaming: false,
            error: None,
            aborted: false,
        }))
    };
    let tool_only_assistant = || {
        ChatEntry::Assistant(Box::new(AssistantMessage {
            blocks: Vec::new(),
            has_tool_calls: true,
            streaming: false,
            error: None,
            aborted: false,
        }))
    };
    let user = || ChatEntry::User {
        text: "hello".to_string(),
    };

    // Nothing preceding: the collapsed form leads with a blank, the
    // expanded form sits flush against the top of the chat.
    let view = view_with(vec![agent_message_row()]);
    assert!(view.conversation_leading(0, false));
    assert!(!view.conversation_leading(0, true));

    // A user row is never a compact neighbor: both forms lead.
    let view = view_with(vec![user(), agent_message_row()]);
    assert!(view.conversation_leading(1, false));
    assert!(view.conversation_leading(1, true));

    // A visible assistant with tool calls carries the trailing space:
    // the next agent message sits flush in both forms.
    let view = view_with(vec![visible_assistant(), agent_message_row()]);
    assert!(!view.conversation_leading(1, false));
    assert!(!view.conversation_leading(1, true));

    // A compact neighbor (tool card, shell completion, agent message):
    // flush collapsed, blank expanded.
    for neighbor in [
        settled_tool_card("c1"),
        shell_completion_row(),
        agent_message_row(),
    ] {
        let view = view_with(vec![neighbor, agent_message_row()]);
        assert!(!view.conversation_leading(1, false), "flush collapsed");
        assert!(view.conversation_leading(1, true), "blank expanded");
    }

    // A tool-only assistant (no visible body) is a separator: the row
    // after it keeps the trailing-space spacing in both forms.
    let view = view_with(vec![tool_only_assistant(), agent_message_row()]);
    assert!(!view.conversation_leading(1, false));
    assert!(!view.conversation_leading(1, true));

    // The backward scan returns at the first non-skippable row it
    // meets: a user row NEWER than the tool-only assistant ends the
    // scan, so the agent message leads (the separator is never
    // reached).
    let view = view_with(vec![tool_only_assistant(), user(), agent_message_row()]);
    assert!(view.conversation_leading(2, false));
    assert!(view.conversation_leading(2, true));
    // With the separator NEWER than the non-compact row, the
    // separator dominates (TS returns the tool separator with a
    // trailing space), so the agent message renders flush.
    let view = view_with(vec![user(), tool_only_assistant(), agent_message_row()]);
    assert!(!view.conversation_leading(2, false));
    assert!(!view.conversation_leading(2, true));
    // A compact row older than the separator ends the scan WITHOUT the
    // separator (TS falls through the `toolSeparator` branch to the
    // compact row): flush collapsed, blank expanded.
    let view = view_with(vec![
        settled_tool_card("c2"),
        tool_only_assistant(),
        agent_message_row(),
    ]);
    assert!(!view.conversation_leading(2, false));
    assert!(view.conversation_leading(2, true));

    // A hidden thinking-only assistant contributes nothing to spacing:
    // the scan skips it to the user row.
    let hidden_assistant = || {
        ChatEntry::Assistant(Box::new(AssistantMessage {
            blocks: vec![MessageBlock::Thinking("quiet".to_string())],
            has_tool_calls: false,
            streaming: false,
            error: None,
            aborted: false,
        }))
    };
    let mut view = view_with(vec![user(), hidden_assistant(), agent_message_row()]);
    view.detail = Detail::Overview;
    assert!(view.conversation_leading(2, false));
}

/// TS `AgentMessageComponent` is a compact neighbor
/// (`isCompactAgentMessageNeighbor`): the hidden thinking of a
/// tool-carrying assistant after an agent message renders ZERO rows
/// -- no leading spacer, no trailing tool separator -- so the tool
/// card sits flush under the agent-message row (the collapsed
/// thinking never leaves a visual gap).
#[test]
fn hidden_thinking_after_an_agent_message_renders_zero_height() {
    let mut view = view_with(vec![
        user_row(),
        agent_message_row(),
        thinking_tool_assistant(),
        settled_tool_card("c1"),
    ]);
    view.detail = Detail::Overview;
    let text = transcript_text(&mut view, 80);
    assert!(!text.contains("thinking body"), "collapsed hides thinking");
    let lines: Vec<&str> = text.lines().collect();
    let agent_row = lines
        .iter()
        .position(|line| line.contains("Agent message - v lane"))
        .expect("the agent-message row renders");
    // The card's panel header is its FIRST row; the seam check must
    // look above it, never inside the panel's own padding.
    let header_row = lines
        .iter()
        .position(|line| line.contains("bash - done"))
        .expect("the tool card header renders");
    // Flush: the row directly above the card header is the agent
    // message block's own last row (its body), never the hidden
    // thinking's trailing spacer (the pre-fix gap).
    assert!(
        agent_row < header_row,
        "the card renders after the agent message:\n{text}"
    );
    assert!(
        lines[header_row - 1].contains("Agent message - v lane"),
        "the agent message header sits directly above the card header:\n{text}"
    );
}

/// A bash execution card is a compact neighbor like the tool cards
/// themselves: the hidden thinking between a `!` bash card and the
/// next tool call renders zero height (TS
/// `isCompactAgentMessageNeighbor` includes
/// `BashExecutionComponent`).
#[test]
fn hidden_thinking_after_a_bash_card_renders_zero_height() {
    let mut view = view_with(vec![
        user_row(),
        ChatEntry::BashExecution(Box::new(crate::bash_card::BashExecutionCard {
            id: "b1".to_string(),
            command: "echo hi".to_string(),
            excluded: false,
            output: "hi".to_string(),
            running: false,
            exit_code: Some(0),
            cancelled: false,
            error_message: None,
            truncated: false,
            full_output_path: None,
            suppress_leading_space: false,
        })),
        thinking_tool_assistant(),
        settled_tool_card("c1"),
    ]);
    view.detail = Detail::Overview;
    let text = transcript_text(&mut view, 80);
    assert!(!text.contains("thinking body"), "collapsed hides thinking");
    let lines: Vec<&str> = text.lines().collect();
    let bash_row = lines
        .iter()
        .position(|line| line.contains("echo hi"))
        .expect("the bash card renders");
    // The tool panel's header is its first row; the seam sits above it.
    let header_row = lines
        .iter()
        .position(|line| line.contains("bash - done"))
        .expect("the tool card header renders");
    // Flush: the row directly above the tool card header is the bash
    // card's own closing border, never a hidden-thinking spacer.
    assert!(
        bash_row < header_row,
        "the card renders after the bash card:\n{text}"
    );
    assert!(
        lines[header_row - 1].contains('-'),
        "the bash card's border sits directly above the card header:\n{text}"
    );
}

/// A visible assistant body after a compact neighbor keeps its own
/// spacers (the collapsed fix only flattens the invisible body).
#[test]
fn a_visible_assistant_after_an_agent_message_keeps_its_spacers() {
    let mut view = view_with(vec![
        user_row(),
        agent_message_row(),
        ChatEntry::Assistant(Box::new(AssistantMessage {
            blocks: vec![MessageBlock::Text("answer body".to_string())],
            has_tool_calls: true,
            streaming: false,
            error: None,
            aborted: false,
        })),
        settled_tool_card("c1"),
    ]);
    view.detail = Detail::Overview;
    let text = transcript_text(&mut view, 80);
    let lines: Vec<&str> = text.lines().collect();
    let agent_row = lines
        .iter()
        .position(|line| line.contains("Agent message - v lane"))
        .expect("the agent-message row renders");
    // In overview the agent message renders its header alone; the
    // visible assistant body then leads with its blank, renders, and
    // keeps the tool separator before the card (TS `hasTrailingSpace`
    // with a visible body).
    assert!(lines[agent_row + 1].trim().is_empty(), "{text}");
    assert!(lines[agent_row + 2].contains("answer body"), "{text}");
    assert!(lines[agent_row + 3].trim().is_empty(), "{text}");
    assert!(lines[agent_row + 4].contains("bash - done"), "{text}");
}

/// The custom rows render through the transcript path: the agent
/// message header plus its guttered body, and the shell-completion row.
#[test]
fn custom_rows_render_in_the_transcript() {
    let mut view = view_with(vec![agent_message_row(), shell_completion_row()]);
    view.detail = Detail::All;
    let text = transcript_text(&mut view, 80);
    assert!(text.contains("Agent message - v lane"));
    assert!(text.contains("`- hi"));
    assert!(text.contains("Background shell command finished"));
    assert!(text.contains("[bash-done]"));
}

/// A streaming assistant message updates across frames: its rows stay
/// out of the cache until the stream settles.
#[test]
fn streaming_assistant_updates_across_frames() {
    let mut view = view_with(vec![ChatEntry::Assistant(Box::new(AssistantMessage {
        blocks: vec![MessageBlock::Text("so far".to_string())],
        has_tool_calls: false,
        streaming: true,
        error: None,
        aborted: false,
    }))]);
    let frame0 = transcript_text(&mut view, 80);
    assert!(frame0.contains("so far"));
    if let Some(ChatEntry::Assistant(open)) = view.chat.get_mut(0) {
        open.blocks = vec![MessageBlock::Text("so far, and more".to_string())];
    }
    view.mark_entry_stale(0);
    let frame1 = transcript_text(&mut view, 80);
    assert!(frame1.contains("and more"));
}

/// The action toast renders as a compact pill row in the live area and
/// auto-dismisses once its TTL passes. Consecutive identical actions
/// coalesce into one refreshed toast (the count bump), never stacked
/// duplicate rows.
#[test]
fn action_toasts_render_as_a_pill_coalesce_and_auto_dismiss() {
    // A transcript taller than the window: the toast still renders in
    // the live area.
    let mut view = view_with(
        (0..40)
            .map(|index| ChatEntry::Status {
                text: format!("covered line {index}"),
                kind: crate::chat::StatusKind::Info,
            })
            .collect(),
    );
    view.toasts.push("Copied to clipboard");
    let frame = composed_rows(&mut view, 60, 24);
    let rows: Vec<String> = frame
        .iter()
        .map(|line| line.iter().map(|span| span.content.as_str()).collect())
        .collect();
    assert!(
        rows.iter().any(|row| row.contains("Copied to clipboard")),
        "the toast renders"
    );
    // The pill reads as a toast chip: the brand-purple Accent color
    // flipped onto the pill's background (REVERSED), not a bare dim
    // line.
    let frame = composed_rows(&mut view, 60, 24);
    let pill = frame
        .iter()
        .flatten()
        .find(|span| span.content.contains("Copied to clipboard"))
        .expect("the pill renders");
    assert!(
        pill.style.add_modifier.contains(Modifier::REVERSED),
        "the pill carries the reversed-chip style: {:?}",
        pill.style
    );
    // Regression (the operator's brand-purple directive): the pill's
    // color is the theme's Accent token -- the brand purple the brand
    // visuals carry -- never the completed-action Success green it
    // replaced.
    assert_eq!(
        pill.style.fg,
        view.theme.fg_style(ThemeColor::Accent).fg,
        "the pill carries the brand-purple Accent style: {:?}",
        pill.style
    );
    assert_ne!(
        pill.style.fg,
        view.theme.fg_style(ThemeColor::Success).fg,
        "the pill must not carry the action green: {:?}",
        pill.style
    );
    // Consecutive identical actions coalesce: the stack holds one
    // toast with the count bump, not stacked duplicate rows.
    view.toasts.push("Copied to clipboard");
    view.toasts.push("Copied to clipboard");
    let frame = composed_rows(&mut view, 60, 24);
    let joined: String = frame
        .iter()
        .map(|line| {
            line.iter()
                .map(|span| span.content.as_str())
                .collect::<String>()
        })
        .collect::<Vec<_>>()
        .join("\n");
    let toast_rows = joined
        .lines()
        .filter(|row| row.contains("Copied to clipboard"))
        .count();
    assert_eq!(
        toast_rows, 1,
        "one coalesced toast row, not stacked: {joined}"
    );
    assert!(
        joined.contains("Copied to clipboard (x3)"),
        "the count bump acknowledges every copy: {joined}"
    );
    // The overlay expires with its TTL.
    view.toasts
        .age_by(crate::toast::TOAST_TTL + std::time::Duration::from_millis(1));
    let frame = composed_rows(&mut view, 60, 24);
    let joined: String = frame
        .iter()
        .map(|line| {
            line.iter()
                .map(|span| span.content.as_str())
                .collect::<String>()
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !joined.contains("Copied to clipboard"),
        "the expired toast is gone: {joined}"
    );
}

/// The browse header inserts BELOW the editor's top row with an empty
/// companion row (TS `CustomEditor.render`'s two header rows), so the
/// content rows shift down two rows while a parked message is selected.
#[test]
fn browse_header_pair_sits_below_the_editor_top_row() {
    let mut v = view();
    v.queue_selected = Some(crate::queued::QueueSelectionItem {
        lane: crate::queued::QueueLane::Steering,
        index: 0,
        text: "turn right".to_string(),
        internal: false,
    });
    let frame = composed_rows(&mut v, 80, 24);
    let joined: Vec<String> = frame.iter().map(text_of).collect();
    // The header truncates at the content width; `browse` sits inside
    // the visible prefix (the strip hint row is absent - the queue is
    // empty here, only the selection is set).
    let header_row = joined
        .iter()
        .position(|row| row.contains("browse"))
        .expect("the queue browse header renders");
    assert!(
        joined[header_row - 1].trim().is_empty(),
        "the editor top row stays above the header: {:?}",
        joined[header_row - 1]
    );
    assert!(
        joined[header_row + 1].trim().is_empty(),
        "the empty companion row follows the header: {:?}",
        joined[header_row + 1]
    );
    assert!(
        joined[header_row + 2].contains("> "),
        "the content rows shift below the header pair: {:?}",
        joined[header_row + 2]
    );
}
// ------------------------------------------------------------------
// The collapsed view (the overview detail level) - the undo of the
// 2026-09-25 condensed activity runs (operator directive
// 2026-09-28): "collapse mode should just be details mode, but
// WITHOUT THINKING BLOCKS". Every activity item renders exactly as
// `details` does; only the thinking blocks are hidden, and the
// Ctrl+O cycle from the collapsed startup reveals the thinking.
// ------------------------------------------------------------------

fn collapsed_view(entries: Vec<ChatEntry>) -> AgentView {
    let mut view = view_with(entries);
    view.detail = Detail::Overview;
    view
}

fn thinking_only() -> ChatEntry {
    ChatEntry::Assistant(Box::new(crate::chat::AssistantMessage {
        blocks: vec![crate::chat::MessageBlock::Thinking("hmm".to_string())],
        has_tool_calls: true,
        streaming: false,
        error: None,
        aborted: false,
    }))
}

fn settled_cards(count: usize) -> Vec<ChatEntry> {
    (0..count)
        .map(|index| settled_tool_card(&format!("card{index}")))
        .collect()
}

/// The operator's new contract: the collapsed view renders EVERY
/// activity item exactly as `details` does - every tool card, every
/// notice, every agent-message row - with ONLY the thinking blocks
/// hidden; nothing condenses (the "N tool calls" summary block is
/// gone at every level).
#[test]
fn the_collapsed_view_renders_every_activity_item_as_details_does() {
    let mut entries = settled_cards(3);
    entries.push(thinking_only());
    entries.push(agent_message_row());
    entries.push(crate::chat::ChatEntry::User {
        text: "go".to_string(),
    });
    entries.extend(settled_cards(2));
    let mut view = collapsed_view(entries);
    let text = transcript_text(&mut view, 80);
    assert!(
        text.matches("bash - done").count() == 5,
        "every tool card renders its own panel rows: {text}"
    );
    assert!(
        text.contains("Agent message - v lane"),
        "the agent-message notice keeps its own row: {text}"
    );
    assert!(
        !text.contains("hi"),
        "the collapsed notice row carries no body preview: {text}"
    );
    assert!(
        !text.contains("tool calls"),
        "no condensed-run summary block renders: {text}"
    );
    assert!(
        !text.contains("hmm"),
        "the collapsed view hides the thinking: {text}"
    );
    // The ONLY difference from `details` is the thinking: the
    // Ctrl+O cycle from the collapsed startup is the
    // thinking-visibility toggle (details-with-thinking).
    view.detail = view.detail.next();
    assert_eq!(view.detail, Detail::Details);
    let details = transcript_text(&mut view, 80);
    assert!(
        details.matches("bash - done").count() == 5,
        "every card keeps its own rows at details: {details}"
    );
    assert!(
        details.contains("Agent message - v lane"),
        "the notice keeps its own row at details: {details}"
    );
    assert!(
        details.contains("hmm"),
        "the thinking is visible at details"
    );
}

/// A live card animates on every pulse frame (the working icon) -
/// the card's own rows, never a condensed block's summary.
#[test]
fn a_running_card_updates_between_frames() {
    let mut view = collapsed_view(Vec::new());
    view.push_entry(crate::chat::ChatEntry::User {
        text: "go".to_string(),
    });
    view.push_entry(ChatEntry::Tool(Box::new(ToolCallCard {
        id: "run_r".to_string(),
        name: "bash".to_string(),
        args: serde_json::json!({"command": "sleep 1"}),
        started: true,
        started_at: Some(std::time::Instant::now()),
        ended_at: None,
        result: None,
        result_partial: false,
        ..Default::default()
    })));
    view.pulse_frame = 0;
    let frame0 = transcript_text(&mut view, 80);
    assert!(
        frame0.contains("running"),
        "the running card renders its own rows: {frame0}"
    );
    view.pulse_frame = 1;
    let frame1 = transcript_text(&mut view, 80);
    assert_ne!(
        frame0, frame1,
        "the working icon animates with the pulse frame"
    );
    assert!(
        !frame1.contains("tool calls"),
        "no condensed block renders while the run is live: {frame1}"
    );
}

/// Streamed cards render their own rows as they arrive - the first
/// card is visible at once (the old condensing waited for the
/// third item before the block appeared).
#[test]
fn streamed_cards_render_their_own_rows_immediately() {
    let streamed = |id: &str| {
        ChatEntry::Tool(Box::new(ToolCallCard {
            id: id.to_string(),
            name: "bash".to_string(),
            args: serde_json::json!({"command": "ls"}),
            started: true,
            started_at: Some(std::time::Instant::now()),
            ..Default::default()
        }))
    };
    let mut view = collapsed_view(Vec::new());
    view.push_entry(crate::chat::ChatEntry::User {
        text: "go".to_string(),
    });
    view.push_entry(streamed("c0"));
    let one = transcript_text(&mut view, 80);
    assert!(
        one.contains("running"),
        "the first streamed card renders at once: {one}"
    );
    view.push_entry(streamed("c1"));
    view.push_entry(streamed("c2"));
    let three = transcript_text(&mut view, 80);
    assert_eq!(
        three.matches("running").count(),
        3,
        "every streamed card keeps its own row: {three}"
    );
    assert!(
        !three.contains("tool calls"),
        "no summary block ever forms: {three}"
    );
}

/// A result landing sent/queued agent-message receipts used to
/// re-derive the condensed run map (the receipts were condensing
/// threshold inputs); now the landing just settles the card and
/// its own rows render - the receipts ride the cell's result
/// details, and nothing else moves.
#[test]
fn a_landing_result_with_receipts_settles_the_card() {
    let mut view = collapsed_view(Vec::new());
    view.push_entry(crate::chat::ChatEntry::User {
        text: "go".to_string(),
    });
    view.push_entry(ChatEntry::Tool(Box::new(ToolCallCard {
        id: "cell".to_string(),
        name: "ipython".to_string(),
        args: serde_json::json!({"code": "print(1)"}),
        started: true,
        started_at: Some(std::time::Instant::now()),
        ..Default::default()
    })));
    let index = view.chat.len() - 1;
    if let Some(ChatEntry::Tool(card)) = view.chat.get_mut(index) {
        card.result = Some(ToolResultView {
            content: vec![serde_json::json!({"type": "text", "text": "done"})],
            details: serde_json::json!({
                "sentAgentMessages": [
                    { "id": "m1", "message": "a", "deliveryStatus": "delivered", "receiverRole": "parent" }
                ]
            }),
            is_error: false,
        });
    }
    view.mark_entry_stale(index);
    let text = transcript_text(&mut view, 80);
    assert!(
        text.contains("python - print(1)"),
        "the settled cell renders its own rows: {text}"
    );
    assert!(
        text.contains("Agent message"),
        "the landed receipt's notice row renders: {text}"
    );
    assert!(
        !text.contains("tool calls"),
        "no condensed block forms on the landing: {text}"
    );
    // The same rows render at `details` (only the thinking would
    // differ, and this transcript has none).
    view.detail = Detail::Details;
    let details = transcript_text(&mut view, 80);
    let collapsed_body = text.replace("Collapsed mode (Ctrl+O to expand)", "MODE");
    let details_body = details.replace("Details mode (Ctrl+O to expand)", "MODE");
    assert_eq!(
        collapsed_body, details_body,
        "the collapsed view renders the activity exactly as details does"
    );
}

/// The settled rows are cacheable: a second render serves the
/// cached rows and they match a fresh render byte for byte.
#[test]
fn settled_rows_survive_a_cache_roundtrip() {
    let mut view = collapsed_view(settled_cards(3));
    let first = transcript_text(&mut view, 80);
    let second = transcript_text(&mut view, 80);
    assert_eq!(first, second, "the cached card rows are stable");
    let mut fresh = collapsed_view(settled_cards(3));
    let fresh_text = transcript_text(&mut fresh, 80);
    assert_eq!(
        first.replace("0s", "").replace("0.0s", ""),
        fresh_text.replace("0s", "").replace("0.0s", ""),
        "a fresh view renders the same rows (the Took clock may move)"
    );
}
