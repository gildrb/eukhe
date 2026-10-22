# Harness laws: interface

The shared rules (what a law secures, the adversary, H1 to H6) are in [harness.md](harness.md).

### S8. The interface

The terminal UI (eukhe-tui) runs fullscreen by default: it paints a
screen-sized frame (a transcript window and the dock) into the
alternate screen. With `terminal.fullscreen` set to `false` it runs
inline: it writes the transcript into the native scrollback of the
terminal and draws a live area below it. The rules below are the
inline terminal's; the fullscreen window renders the same entries.

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
   gets no separator. A new transcript of a session does not hold the
   kernel restore notices that the view showed before: each restore
   shows its notice one time ([daemon.md](daemon.md) D1).
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
   then, at the one token estimate: 3.5 characters (UTF-16 code units)
   for each token, rounded up. The compaction threshold and the context
   usage of the tray use the same estimate.
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
   arguments at 3.5 characters for each token. The rate shows after
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
`PROOF.bend` section `screen`. Every input is free: any blocks, growths,
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

#### Keys

The keys below operate at the prompt. An open menu, picker or panel gets
each key first: in the settings menu, Shift+Tab goes to the previous tab
and does not change the thinking level.

| Key | Action | Effect |
| --- | --- | --- |
| Shift+Tab | `app.thinking.cycleForward` | Set the next thinking level that the model offers. After the last level, go to the first. |
| Shift+Alt+Tab | `app.thinking.cycleBackward` | Set the previous thinking level that the model offers. Before the first level, go to the last. |

The daemon command is `cycle_thinking_level` with a `direction`. A model
with fewer than two levels keeps its level, and the status row shows
`Current model offers no other thinking level`. Otherwise the tray label
and the `Thinking level: <level>` status row show the new level. `/effort`
shows the levels that the model offers and marks the current level. A
session with no level yet shows no level, never `off`.

Code: `eukhe-tui/src/keybindings/definitions.rs` (the defaults);
`session_ui/keys.rs` (the key arms); `session_ui/model_picker.rs`
`cycle_thinking_level`, `show_thinking_level`. Tests:
`tests/effort_tray_label_headless.rs`.

#### Turn visibility

From the Enter to the end of the turn the working indicator is on, and
only while work runs: the prompt travels or waits for its turn, a turn
of its run is unanswered, or a compaction runs. The reply streams with
it on: an answer whose text is still behind its pace when the turn ends
keeps the row up, as the end left it, until the frame that shows the
last of the text. One clock counts from
the Enter through the run's requests, retries, compactions and a
re-attach. A rebuild of the chat (a re-attach, a worker replacement, a
reconnect) derives the indicator from the snapshot and this window's own
prompt: a prompt still traveling or queued keeps it, a turn whose answer
is stored does not raise it, and a compaction outside a turn shows and
then ends. A late prompt ack never raises it again (the run already
ended, or the session closed).

A turn that ends without an answer leaves exactly one row that says so
and names the next step: the failure (with `/login`, the provider's key
or `/model` for a missing key), the retry episode's outcome line, `The
turn ended without a reply` (a blank answer, a turn the engine reported
nothing for, a run that ended before its first request or after a tool
round), the refused or lost prompt (the draft returns to the editor, or
wait and resend), or the closed session (reopen it from Agents View). A
lost prompt's row retires when the turn shows after all. A reopened chat
folds the same rows from the stored transcript (`snapshot::fold_transcript`
with `TurnTail`): the end row of each ended turn, one line per retry
episode whichever order its rows were stored in, and a reply that
streamed text before its failure keeps the text, not a second error. The
rows only this window holds (a refused or lost prompt, a closed session)
survive a rebuild of the same session. The `Primary provider recovered`
notice is a toast, since no transcript records it.

Laws (a draft): `LAWS.bend` section `turn_visibility` on the model in
`bend/turn_visibility.bend`. Code: `session_ui/apply.rs`
(`apply_update`), `session_ui/prompt.rs` (`apply_prompt_outcome`),
`session_ui/lifecycle.rs` (`attach_session`, `rebuild_view`),
`snapshot.rs` (`fold_transcript`, `reconstruct`), `snapshot/turn_end.rs`,
`view.rs` (`start_loader`, `stop_loader`, `loader_row`) with
`view/streaming.rs` `advance_paces` (the row through the reveal).
Tests: `tests/turn_visibility_headless.rs` (the findings' live histories),
`snapshot::tests::turn_end`, `tests/failed_turn_visible_headless.rs`,
`view::screen_tests::the_loader_stays_up_until_the_streamed_text_all_shows`.

### T1. Themes

One theme source serves the terminal UI and the HTML export (`/export`,
`eukhe session export`). The crate `eukhe-theme` holds the theme files,
the validator, the name resolver and the color math. The terminal UI
and the export use the same functions.

#### The theme file

A theme file is JSON. Its schema is `theme-schema.json`, next to the
bundled themes in `crates/eukhe-theme/themes/` (`eukhe`, `dark`,
`light`).

- `name`: the name the theme resolves by.
- `vars`: named colors. A color value that is not a color names a
  variable. The validator resolves each reference once, when it reads
  the file. A missing variable or a cycle makes the file invalid.
- `colors`: one color per token. A color is `#rrggbb` (a `#` and six hex
  digits), `""` (the terminal default) or an xterm-256 index 0 to 255.
  Any other value, an unknown token or a missing required token makes
  the file invalid.
- `export`: the optional `pageBg`, `cardBg` and `infoBg` of the HTML
  export. Without them, the export derives the three backgrounds from
  `userMessageBg`.

The optional tokens fall back as follows:

- `mdBody` falls back to `text`.
- `background` falls back to `export.pageBg`, then to `userMessageBg`,
  then to the background of the default theme.
- `foreground`, `refinementHeader` and `refinementSummary` fall back to
  the builtin theme of the same mode: `eukhe` for a dark theme, `light`
  for a light theme.

The mode comes from the background, never from the name. A theme is
light when the WCAG relative luminance of its background is above one
half.

In the HTML export, every token is a CSS variable (`--<token>`) with a
`#rrggbb` value. The terminal default (`""`) paints the foreground on a
text token and the background on a surface token (the tokens that end
in `Bg`, and `background`). `template.css` has no color of its own: it
reads only these variables.

#### Which theme

The `theme` setting names the theme (`/settings`). When the setting is
empty, the theme is `eukhe` on every surface. A name resolves by the
`name` in the file, in this order:

1. The registered files: the `themes` arrays of the settings, the
   packages and the project directories, then the `--theme` paths.
2. The builtin themes.
3. The files in `<agent-dir>/themes/`.

The first valid file with the name wins. A second valid file with the
same name gives a collision warning. A name that no valid theme has
resolves to `eukhe`, with a warning. Resolution never fails.

The export uses the same sources as the terminal UI. The TUI sends its
registered files with `/export` (`themePaths`). The daemon resolves the
resource themes of the session when a client sends none (the
dashboard). `eukhe session export` reads the `theme` setting and the
`--theme` and `--no-themes` flags.

#### Laws

`LAWS.bend` section `themes` (T1) states the laws on the model in `bend/theme.bend`
and `bend/color.bend`. `PROOF.bend` section `themes` proves them:

- The empty name resolves to the default theme. A name resolves to the
  first valid theme that has it. A name that no valid theme has resolves
  to the default theme with a warning.
- A loaded file is valid, and the palette of a valid file defines every
  token.
- The mode follows the background. The name changes neither the palette
  nor the mode.
- In each shipped theme, every text token meets 4.5:1 against its
  background and every non-text token (borders, rules, the effort ramp
  ends) meets 3:1. The user and custom message texts are measured on their
  own surfaces. The contrast is an exact integer comparison.
- In each shipped theme, the status colors (accent, success, warning,
  error) stay distinct in a 256-color terminal.

The bridge test `crates/eukhe-core/src/export_html/theme_bridge.rs` runs
the Rust code and the model on the same scenarios. It checks that the
model's tables equal the theme files, and that resolution, validation,
luminance, contrast and the 256-color mapping agree.

### T3. Terminal colors

The terminal UI paints only theme colors. The crate `eukhe-tui` has one
module that can make a color: `src/theme.rs`. The value of
`theme::Color` is private to it, so the compiler refuses a color literal
in any other module, tests included. Other code gets each color from a
`Theme`: a token of the theme file, or a value that `theme.rs` computes
from the tokens. The exit resume hint that `eukhe-cli` prints comes
from the TUI in the theme's `dim` color.

#### The tokens

- `effortLow` and `effortHigh`: the ends of the effort ramp. A model
  offers a ladder of n effort levels, of any length. Rung k (1 to n) of
  the ramp takes, in each channel, the lower end of the channel plus
  floor(d * w / n). d is the channel distance. w is k when the channel
  rises from `effortLow` to `effortHigh`, and n - k when it falls. So
  rung n is `effortHigh`, and the ramp starts one step above
  `effortLow`. In the `/model` picker, each filled effort square of the
  selected row has its rung.
- `contextHigh`: the context usage tone between `warning` and `error`.
- `liftLight` and `liftDark`: the colors that a selection band moves
  toward when it is too near its surface: `liftLight` when the
  selection is lighter than the surface, `liftDark` when it is darker.
  The onboarding wash lifts the theme's background 8% toward
  `liftLight` on a dark theme and toward `liftDark` on a light theme.

#### The usage bands

The status line shows the context usage of the window that the daemon
serves (`contextUsage.contextWindow`). Its tone is `dim` below half the
window, `warning` from 1/2, `contextHigh` from 7/10 and `error` from
9/10. A band is reached when window * num <= tokens * den, exactly. An
unknown window (0) reaches no band. No band is a token count, so every
window turns at the same share of its size.

#### Laws

`LAWS.bend` section `tui_color` (T3) states the laws on the model in
`bend/tui_color.bend`, with the theme tables of `bend/theme.bend`.
`PROOF.bend` section `tui_color` proves them:

- The effort ramp has one rung for each level. For any ladder length,
  each channel moves from `effortLow` toward `effortHigh`, never back.
  For any ladder length up to the widest channel distance of the ends,
  no two rungs have the same color. In each shipped theme, no two rungs
  have the same color for any ladder of the level vocabulary.
- Each usage band is a fraction of the window above 0 and at most 1,
  above the band before it. More tokens in the same window never give a
  lower band. The band depends only on the fraction of the window in
  use: the same fraction of a window k times as large gives the same
  band.
- Every color role of the terminal UI resolves in the palette of every
  valid theme file, and paints a color in every shipped theme.

The bridge test `crates/eukhe-tui/src/theme/bridge.rs` runs the Rust
ramp, the shipped ramps, the bands and the roles against
`bend/bridge_tui_color.bend`.
