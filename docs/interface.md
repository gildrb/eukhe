# Harness laws: interface

The shared rules (what a law secures, the adversary, H1 to H6) are in [harness.md](harness.md).

### S8. The interface

The inline terminal (eukhe-tui) writes the transcript into the native
scrollback of the terminal and draws a live area below it.

The transcript:

1. Each chat entry is active (it can change), final (its rows are
   fixed), or committed (its rows are in the scrollback). An entry is
   final when it settles: a message that stopped streaming and shows all
   its text, a tool card with its result, and so on (`entry_settled`).
2. Each frame is one flush. The flush commits the final entries in
   order, up to the first active entry. Thus the committed entries are a
   prefix of the chat, with no gap. Their rows go into the scrollback
   with this frame, at the width of this frame.
3. Committed rows are never written again. The writer does not clear the
   screen or the scrollback for them.
4. Resize policy "preserve". On a width change the scrollback stays as
   the terminal reflowed it. The writer finds where the reflow put the
   live area and draws only the live area again, at the new width. Rows
   committed after the change use the new width.
5. A new theme, detail level (Ctrl+O), image setting, or code indent
   applies to the live area and to the rows committed after it. The
   scrollback keeps the rows as it got them.
6. An edit to a committed entry (a late tool-card state, a status row
   that changes) does not change the scrollback. The inline terminal
   does not show the edit. The fullscreen window renders the entry again
   and shows it.
7. The first paint writes the splash and the history so far.
8. A new transcript (a session switch, `/new`, a fork or tree move, a
   reconnect resync, a `/reload`, a transcript rebuild) is a new run of
   the model, not an edit. The scrollback keeps the old transcript as
   written. When the old one has entries there, the first frame of the
   new one writes one dim separator row that names the break (new
   session, reconnected, or transcript rebuilt) and the session, and the
   new history commits below it. A scrollback that holds only the splash
   gets no separator.
9. After the first paint, the inline terminal never clears the screen or
   the scrollback (no `ESC[2J`, no `ESC[3J`). Fullscreen mode repaints
   its own alternate screen, which has no scrollback. There is no user
   command that draws the screen again in full. Thus the protocol has no
   exception.

Pacing. Streamed assistant text shows at a pace. Each frame shows at
least `min` more characters of the backlog (when there is backlog), and
`1/(1+lag)` of the backlog when that is more. The screen never shows text
that did not arrive, and never shows less than before. When the stream
ends, the frames go on until all the text shows. Then the message
settles. The settings are `terminal.streamPace.minChars` (default 2; 0
reads as 1) and `terminal.streamPace.lag` (default 3). At the 16 ms frame
gate, a burst of 400 characters shows in 19 frames, about 300 ms. A
change of the detail level (Ctrl+O) that shows or hides thinking is not
text that arrived. The text on the screen stays where it was, and the
thinking that the change shows above that text is on the screen
immediately.

Generation speed. The status line shows the speed of the model request,
after the model segment. The setting is `terminal.showSpeed` (default
true). `/toggle terminal.showSpeed` hides or shows the segment at once.

1. Prefill. A turn starts a model request. Until the first token, the
   segment shows `prefill <elapsed>s`. After the first response of the
   session, it also shows an estimate of the prompt tokens that the cache
   does not hold: `prefill 3.2s (~1.2K tok)`. The estimate is the output
   of the last response plus the user text and the tool results since
   then, at 4 characters for each token.
2. Prefill progress. A llama.cpp `llama-server` sends its progress
   through the prompt when the request sets `return_progress`
   (`prompt_progress`: `total`, `cache`, `processed`, `time_ms`). The
   request sets it when the quirks rulebook gives the host
   `prompt_progress` (provider `llama.cpp` or `llama-cpp`), or when
   `compat.supportsPromptProgress` is true. The worker sends each report
   to the clients as a `prompt_progress` session event. The segment then
   shows `prefill <processed>/<total> tokens`. The other providers keep
   the elapsed time.
3. Decode. When the first token shows, the segment shows
   `decode N tok/s`: the output tokens after the first one, divided by
   the time since the first token. The token count is the count of the
   provider when it streams one, else the streamed text and tool
   arguments at 4 characters for each token. The rate shows after
   250 ms of decode.
4. Summary. When the response settles, the segment shows the exact
   rates from the usage and the stream marks of the provider, until the
   next turn: `prefill X tok/s (TTFT Ys) · decode Z tok/s`. The prefill
   rate is the uncached prompt tokens (input and cache write) divided by
   the time to first token (TTFT). When the cache gave 95 % or more of
   the prompt, the segment shows `prefill cached (TTFT Ys)`. Without a
   prompt count, it shows `TTFT Ys` only. A failed or stopped response
   shows no segment.

The stream marks come from `AssistantMessageEventStream`. On the final
message it sets `timing` (`firstByteMs`, `firstTokenMs`, `lastTokenMs`:
milliseconds after `timestamp`, the request start) with `durationMs`.
The first byte is the `start` event. The first and the last token are the
text, thinking and tool-call start and delta events. A message without
`timing` uses the times that the client saw. The segment does not stop a
frame: the status line reads the clock at the frame, and no disk or
network work occurs.

Code: `eukhe-tui/src/gen_speed.rs` `SpeedClock`, `SpeedPhase`,
`SpeedSample`, `ResponseSpeed`; `status_line.rs` `render_status_line`;
`session_ui/apply.rs` (the clock follows the turn events);
`eukhe-ai/src/utils/event_stream.rs` (`timing`);
`api/openai_completions/streaming.rs` `parse_prompt_progress`. Tests:
`gen_speed::tests` (the rate math), `tests/gen_speed_headless.rs` (a
scripted provider turn with timed events: each phase on the status line,
and the setting off).

Off-screen check. A virtual terminal (`vt.rs`) holds the screen as the
writer left it. Each frame runs on a copy of it first:

1. The check compares the result with the frame. The rows above the
   live area keep their cells. The last history rows of the frame end
   right above the live area. The check compares only the last rows, as
   many as the screen height. History rows that scroll past the screen
   (for example, most of a 5,000-row first paint) are not checked. Each
   live block that changed, or that the bytes rewrote, reads as it does
   written on a blank screen. The rows below the live area are blank. The
   cursor is where the writer tracks it.
2. A frame that fails is drawn again in full (the whole live area) and
   checked again. A frame that fails both checks is not written. The
   agent log (`<agent dir>/logs/agent.jsonl`, component `tui-render`)
   records it, and a toast shows it. Its history rows go out before the
   history of the next frame.
3. When three frames in a row fail both checks
   (`REJECTED_FRAMES_LIMIT`), the paint fails with `ScreenCheckFailed`.
   The surface ends, the terminal is restored, and the error names the
   failure and the log. The screen does not freeze.
4. A release (exit, suspend, a child process) with history rows still
   pending does not write them unchecked. It reports them, and the next
   frame writes them.

The cost of the check, for a 40-row live area at 120 x 50 under 5,000
history rows (`verify_cost_on_a_large_transcript`): in release, a
streaming frame takes 47 µs mean (114 µs max) with the check, of which
the check is 13 µs (34 µs max). The first frame, which writes all 5,000
history rows, takes 30 ms, of which the check is 12 ms. In a dev build:
254 µs per streaming frame, of which the check is 117 µs. Both are far
below the 16 ms frame.

Layout. The live area is a vertical stack (`stack::vstack`) above the
dock: the unsettled entries, the transcript tail, then the toasts. Each
child is cut from its top, newest first, to the rows that the dock
leaves. Then the stack places them from the top, one under the other:
no child is outside the viewport, no two overlap, and a child that fits
is drawn whole.

Components. Tool cards (ipython, bash, generic) build an element tree
(`element.rs`: `Text`, `Row`, `Column`, `Inset`, `Panel` with a title, a
status, a fill and children). One renderer draws the panel header, the
status icons (the animated working icon too), the fill, the padding and
the semantic colors. No card draws its own chrome.

Model: `bend/screen.bend`. Laws: `LAWS.bend` section (S8). Proofs:
`bend/proof_screen.bend`. Every input is free: any blocks, growths,
finals, flushes and resizes in any order; any chunk sizes and frames;
any check results; any child heights.

| Law | Says |
| --- | --- |
| `tx_gapless` | The committed blocks come first: the scrollback has no gap (S8.2). |
| `tx_scrollback_append_only` | The scrollback only grows: a committed block stays, unchanged, in its place, whatever comes after (S8.3). |
| `tx_resize_keeps` | A resize writes no block again (S8.4). |
| `tx_flush_settles` | After a flush no final block waits: the first block not committed is active (S8.2). |
| `pace_never_ahead` | The screen never shows text that did not arrive (pacing). |
| `pace_never_back` | The screen never shows less than before (pacing). |
| `pace_drains` | With a minimum of at least 1, a backlog of b characters all shows after b frames (pacing). |
| `verify_only_checked` | Only a frame that passed its check reaches the terminal; a frame that failed both checks is reported (check 2). |
| `layout_inside` | No child is drawn outside the viewport (layout). |
| `layout_apart` | No two children overlap (layout). |
| `layout_whole_when_room` | Children that fit are drawn whole (layout). |

Code: `eukhe-tui/src/view/ledger.rs` `Ledger` (`open`, `grow`, `finish`,
`flush`, `resize`), `Phase`; `view/frame.rs` `AgentView::compose`
(one flush per frame), `FrameStart`, `Scrollback`, `TranscriptBreak`,
`transcript_break_row` (the separator), `compose_live`;
`view/stack.rs` `vstack`, `stack_rows`; `pace.rs` `Pace`, `PaceRate`,
`reveal`; `view/streaming.rs` `advance_paces`, `paced_message`;
`view.rs` `mark_entry_stale`, `clear_chat`, `note_resize`, `is_pacing`;
`inline_term.rs` `InlineTerminal::paint` (the check), `present`,
`Check`, `Shown`, `Painted`, `Rejection`, `ScreenCheckFailed`,
`REJECTED_FRAMES_LIMIT`, `set_width` (the live redraw after a reflow),
`release`; `vt.rs` `Vt`; `element.rs`
`Element`, `Panel`, `render`; `tool_card/*` (the cards as elements);
`app.rs` `draw`, `draw_fullscreen`, `show_rejection`;
`interactive/run.rs` (the resize arms, the pace wake, the log hook);
`client_settings.rs` `stream_pace`, `log_render_error`.

Tie: the bridge test
`view::bridge::the_rust_interface_equals_the_bend_model` runs `Ledger`,
`Pace`, `present` and `vstack` against `bend/bridge_screen.bend` on 600
generated scenarios (opens, growths, finishes, flushes and resizes on
blocks that exist and that do not; chunks of zero and minimums of zero;
all four check pairs; children that fit and that do not) and compares
the transcripts byte for byte. eukhe-tui may not depend on
eukhe-durable, so `src/testing.rs` holds a copy of the bridge runner.
Regression tests: `view::screen_tests` (committed rows are written once
through a width change, a detail change and an edit; a new transcript
starts below a separator and keeps the old rows on the virtual
terminal, with no clear; streamed text shows at its pace and commits
whole; the
live stack keeps the newest rows above the dock); `inline_term::tests`
(`a_resize_keeps_scrollback_and_redraws_only_the_live_area`,
`a_desynced_live_area_is_redrawn_whole`,
`a_frame_both_checks_reject_is_not_written_and_its_history_waits`,
`rejections_in_a_row_end_the_surface_and_are_logged`,
`present_follows_the_model_table`,
`a_full_width_last_row_keeps_its_last_cell_below_history`); `vt::tests`;
`pace::tests`; `view::ledger::tests`; `view::stack::tests`;
`element::tests` and `tool_card::golden_tests` (the cards render the
same rows as before the element tree);
`tests/chat_view_startup_headless.rs` (Ctrl+O does not write a
committed row again). Not modelled: where the reflow of a terminal puts
the live area (an estimate, checked by the virtual terminal), and the
map from entries to rows. Their tests tie them.
