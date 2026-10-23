# Harness laws: interface

Shared rules (what a law secures, the adversary, H1 to H6): [harness.md](harness.md).

### S8. The interface

Terminal UI (eukhe-tui): fullscreen by default, painting a screen-sized frame (transcript window, dock) into the alternate screen. `terminal.fullscreen` = `false`: inline, writing the transcript into the terminal's native scrollback with a live area below. Rules below are the inline terminal's; fullscreen renders the same entries.

Transcript:

1. Entry states: active (can change), final (rows fixed), committed (rows in scrollback). Final = settled (`entry_settled`): e.g. a message done streaming with all text shown, a tool card with its result.
2. One flush per frame: commits final entries in order up to the first active one. Committed entries = gapless chat prefix; their rows enter scrollback with this frame, at its width.
3. Committed rows never rewritten; writer never clears screen or scrollback for them.
4. Resize policy "preserve": on width change scrollback stays as the terminal reflowed it; writer finds where reflow put the live area and redraws only it, at the new width. Later commits use the new width.
5. New theme, detail level (Ctrl+O), image setting or code indent: applies to live area and later commits; scrollback keeps rows as received.
6. Edit to a committed entry (late tool-card state, changing status row): scrollback unchanged; inline terminal does not show it; fullscreen re-renders and shows it.
7. First paint writes the splash and history so far.
8. New transcript (session switch, `/new`, fork or tree move, reconnect resync, `/reload`, transcript rebuild) = new model run, not an edit. Scrollback keeps the old transcript. If the old one has entries there, the new first frame writes one dim separator row naming the break (new session, reconnected, or transcript rebuilt) and the session; new history commits below. Splash-only scrollback: no separator. A session's new transcript omits previously shown kernel restore notices: each restore shows its notice once ([daemon.md](daemon.md) D1).
9. After first paint the inline terminal never clears screen or scrollback (no `ESC[2J`, no `ESC[3J`). Fullscreen repaints its own alternate screen (no scrollback). No user command redraws the full screen: the protocol has no exception.

Pacing (streamed assistant text):

- Per frame: at least `min` more backlog characters (if backlog), or `1/(1+lag)` of backlog if more.
- Never shows unarrived text; never shows less than before.
- After stream end, frames continue until all text shows; then the message settles.
- Settings: `terminal.streamPace.minChars` (default 2; 0 reads as 1), `terminal.streamPace.lag` (default 3).
- Example: 16 ms frame gate, 400-character burst: 19 frames, ~300 ms.
- Ctrl+O detail change showing/hiding thinking is not arrived text: on-screen text stays put; thinking shown above it appears at once.

Generation speed: status-line segment after the model segment. Setting `terminal.showSpeed` (default true); `/toggle terminal.showSpeed` applies at once.

1. Prefill. Until first token: `prefill <elapsed>s`. After the session's first response, plus an uncached prompt-token estimate: `prefill 3.2s (~1.2K tok)`. Estimate = last response output + user text and tool results since, at 3.5 characters (UTF-16 code units) per token, rounded up. Compaction threshold and tray context usage use the same estimate.
2. Prefill progress. llama.cpp `llama-server` reports prompt progress when the request sets `return_progress` (`prompt_progress`: `total`, `cache`, `processed`, `time_ms`). Set when the quirks rulebook gives the host `prompt_progress` (provider `llama.cpp` or `llama-cpp`), or `compat.supportsPromptProgress` is true. Worker forwards each report as a `prompt_progress` session event; segment shows `prefill <processed>/<total> tokens`. Other providers: elapsed time.
3. Decode. From first token: `decode N tok/s` = output tokens after the first / time since first token. Count: provider's streamed count, else streamed text and tool arguments at 3.5 characters per token. Shown after 250 ms of decode.
4. Summary. Response settled, until next turn: exact rates from provider usage and stream marks: `prefill X tok/s (TTFT Ys) · decode Z tok/s`. Prefill rate = uncached prompt tokens (input + cache write) / time to first token (TTFT). Cache ≥ 95 % of prompt: `prefill cached (TTFT Ys)`. No prompt count: `TTFT Ys` only. Failed or stopped response: no segment.

- Stream marks: `AssistantMessageEventStream` sets `timing` on the final message (`firstByteMs`, `firstTokenMs`, `lastTokenMs`: ms after `timestamp`, the request start) with `durationMs`. First byte: `start` event. First/last token: text, thinking, tool-call start and delta events. No `timing`: client-observed times.
- Segment never stalls a frame: clock read at the frame; no disk or network work.

Code: `eukhe-tui/src/gen_speed.rs` `SpeedClock`, `SpeedPhase`, `SpeedSample`, `ResponseSpeed`; `status_line.rs` `render_status_line`; `session_ui/apply.rs` (clock follows turn events); `eukhe-ai/src/utils/event_stream.rs` (`timing`); `api/openai_completions/streaming.rs` `parse_prompt_progress`. Tests: `gen_speed::tests` (rate math), `tests/gen_speed_headless.rs` (scripted timed provider turn: each phase on the status line, setting off).

Off-screen check: a virtual terminal (`vt.rs`) holds the screen as the writer left it; each frame runs on a copy first.

1. Compare result with frame: rows above the live area keep their cells; the frame's last history rows end right above the live area. Only the last screen-height rows are compared; history scrolled past (e.g. most of a 5,000-row first paint) is unchecked. Each changed or rewritten live block reads as if written on a blank screen. Rows below the live area blank. Cursor where the writer tracks it.
2. Fail: redraw in full (whole live area), check again.
3. Fail both: draw on a blank screen, check a third time. On the terminal, on-screen rows scroll into scrollback first: no text lost. Resyncs a shadow screen that diverged from the writer's tracked rows.
4. Fail all three: not written; toast shows it. Agent log (`<agent dir>/logs/agent.jsonl`, component `tui-render`) records the 1st, 2nd, 4th, 8th (and so on) consecutive rejection. Its history rows go out before the next frame's history.
5. A check never ends the surface; only user quit or a failed terminal write does.
6. Release (exit, suspend, child process) with pending history rows: not written unchecked; reported, written by the next frame.

Row text: writer keeps only printable characters, tabs (three spaces), SGR sequences, OSC 8 hyperlinks. Drops all other control characters (`\r`, `\n`, backspace, BEL, NEL) and escape sequences (cursor moves, erases): width measure counts them as zero columns, so one kept would shift the cursor and every later row by one.

Check cost, 40-row live area, 120 x 50, 5,000 history rows (`verify_cost_on_a_large_transcript`), all far below the 16 ms frame:

|Build|Frame|Total|Check|
|---|---|---|---|
|release|streaming|47 µs mean (114 µs max)|13 µs (34 µs max)|
|release|first (writes 5,000 history rows)|30 ms|12 ms|
|dev|streaming|254 µs|117 µs|

Layout: live area = vertical stack (`stack::stack_rows`, model `vstack`) above the dock: unsettled entries, transcript tail, toasts. Each child cut from its top, newest first, to the rows the dock leaves; placed from the top, one under another: none outside the viewport, none overlapping, a fitting child drawn whole.

Components: tool cards (ipython, bash, generic) build an element tree (`element.rs`: `Text`, `Row`, `Column`, `Inset`, `Panel` with title, status, fill, children). One renderer draws panel header, status icons (animated working icon too), fill, padding, semantic colors. No card draws its own chrome.

Model: `bend/screen.bend`, run by the compiled Bend core (`eukhe-bend`, entry `bend/ffi_screen.bend`): ledger, pace, stack and paint decision are the model, one core call each per frame (paint decision: one more per failed check). Laws: `laws/screen.bend` (S8 and the entry). Proofs: `proof/screen/`. Free inputs: any blocks, growths, finals, flushes, resizes in any order; any chunk sizes and frames; any check results; any child heights. Rust saturates every count it sends at the wire's largest Nat (10^14 - 1): a lag or minimum at its largest (`terminal.streamPace`) reveals as one past every backlog would.

| Law | Says |
| --- | --- |
| `tx_gapless` | Committed blocks first: scrollback has no gap (S8.2). |
| `tx_scrollback_append_only` | Scrollback only grows: a committed block stays unchanged in place, whatever follows (S8.3). |
| `tx_resize_keeps` | Resize rewrites no block (S8.4). |
| `tx_flush_settles` | After a flush no final block waits: first uncommitted block is active (S8.2). |
| `pace_never_ahead` | Screen never shows unarrived text (pacing). |
| `pace_never_back` | Screen never shows less than before (pacing). |
| `pace_drains` | Minimum ≥ 1: a b-character backlog fully shows within b frames (pacing). |
| `verify_only_checked` | Only a frame passing its check reaches the terminal; one failing both checks is reported (check 2). |
| `paint_first_passing_check` | First passing check picks what reaches the terminal: frame, full redraw or fresh redraw. All three fail: nothing drawn, surface goes on (checks 3 to 5). |
| `layout_inside` | No child outside the viewport (layout). |
| `layout_apart` | No two children overlap (layout). |
| `layout_whole_when_room` | Fitting children drawn whole (layout). |
| `pace_reveal_formula`, `pace_lag_at_cap` | A frame reveals min(b, max(min, b / (1 + lag))); a lag ≥ backlog reveals the minimum: a saturated lag never overflows (pacing). |
| `tx_committed_inert` | Committed blocks are inert: the core runs a frame's events on the blocks after the committed prefix alone (S8.3). |
| `screen_ffi_run`, `screen_ffi_pace`, `screen_ffi_stack` | Core entry answers exactly the model's transcript, pace and placement for every request Rust writes. |
| `screen_ffi_paint` | After any number of checks, the entry asks for the next check exactly while every check so far failed (fewer than three), else answers the paint of the first passing check, whatever unrun checks would answer (checks 2 to 4). |

Code: `eukhe-tui/src/view/ledger.rs` `Ledger` (`apply`: a frame's events, one core call; `truncate`, outside the model), `Event`, `Phase`; `bend_core.rs` `decide` (one core call); `view/frame.rs` `AgentView::compose` (one ledger call per frame), `FrameStart`, `Scrollback`, `TranscriptBreak`, `transcript_break_row` (separator), `compose_live`; `view/stack.rs` `stack_rows`; `pace.rs` `Pace` (`frame`: one core call; `shrink_to`, `recount` outside the model), `PaceRate`; `view/streaming.rs` `advance_paces`, `paced_message`; `view.rs` `mark_entry_stale`, `clear_chat`, `note_resize`, `is_pacing`; `inline_term.rs` `InlineTerminal::paint` (check), `paint_decision` (compiled paint decision), `Attempt`, `Check`, `Painting`, `Painted`, `Rejection`, `cells_only`, `set_width` (live redraw after reflow), `release`; `vt.rs` `Vt`; `element.rs` `Element`, `Panel`, `render`; `tool_card/*` (cards as elements); `app.rs` `draw`, `draw_fullscreen`, `show_rejection`; `interactive/run.rs` (resize arms, pace wake, log hook); `client_settings.rs` `stream_pace`, `log_render_error`.

Tie: ledger, pace, stack and paint decision are the model (compiled core); no bridge. Only Rust can build a redraw, so the core decides one step at a time: Rust sends the checks run so far; the core answers the paint or asks for the next redraw's check (law `screen_ffi_paint`); a redraw is built only when asked. `inline_term::tests::paint_decision_builds_each_redraw_only_when_asked` checks that shell on all eight check triples.

Regression tests:

- `view::screen_tests`: committed rows written once across width change, detail change, edit; new transcript below a separator, old rows kept on the virtual terminal, no clear; streamed text paced, committed whole; live stack keeps newest rows above the dock.
- `inline_term::tests`: `a_resize_keeps_scrollback_and_redraws_only_the_live_area`, `a_desynced_live_area_is_redrawn_whole`, `a_frame_both_checks_reject_is_not_written_and_its_history_waits`, `rejections_in_a_row_never_end_the_surface`, `control_characters_in_rows_never_move_the_cursor`, `frames_that_keep_the_contract_are_always_drawn`, `paint_decision_builds_each_redraw_only_when_asked`, `a_full_width_last_row_keeps_its_last_cell_below_history`.
- `vt::tests`, `pace::tests`, `view::ledger::tests`, `view::stack::tests`.
- `element::tests`, `tool_card::golden_tests` (cards render the same rows as before the element tree).
- `tests/chat_view_startup_headless.rs` (Ctrl+O does not rewrite a committed row).

Not modelled (tied by tests): where terminal reflow puts the live area (estimate checked by the virtual terminal); entry-to-row map.

#### Keys

At the prompt. An open menu, picker or panel gets keys first (settings menu: Shift+Tab = previous tab, thinking level unchanged).

| Key | Action | Effect |
| --- | --- | --- |
| Shift+Tab | `app.thinking.cycleForward` | Next thinking level the model offers; wraps last → first. |
| Shift+Alt+Tab | `app.thinking.cycleBackward` | Previous thinking level the model offers; wraps first → last. |

- Daemon command: `cycle_thinking_level` with `direction`.
- Model with < 2 levels keeps its level; status row `Current model offers no other thinking level`. Else tray label and `Thinking level: <level>` status row show the new level.
- `/effort` lists the model's levels, marks the current one.
- Session with no level yet shows none, never `off`.

Code: `eukhe-tui/src/keybindings/definitions.rs` (defaults), `session_ui/keys.rs` (key arms), `session_ui/model_picker.rs` `cycle_thinking_level`, `show_thinking_level`. Tests: `tests/effort_tray_label_headless.rs`.

#### Slash commands

A slash command alone on the prompt, cursor at its end: the path rules decide (Bend model `bend/command.bend`, entry `bend/ffi_command.bend`, one core call per menu, key or submit).

- Table: one row per declared path (command, registry subcommand, argument value), names lowercase. Flags: `run` (bare path runs: a default or no child), `free` (a word naming no child starts the argument text: commands without registry subcommands, so `/tier x` and `/effort x` reach their handlers' error with the daemon's list), `arg` (text expected after it).
- Sources: `eukhe-types/src/slash_commands.rs` (`subcommands`, `subcommand_optional`, `Subcommand {name, description, usage}`; `/model` roles from `ModelRole::ALL`); argument lists by path from `session_ui.rs` `update_model_eligibility_filters` (`tier`, `effort`, `workflows size`, `dynamic-workflow --size`).
- `resolve(line)`: `Runs{path, args}` (args as typed), `Opens{path}` (bare path, no default), `Unknown{path, word}`, `NoCommand` (first word names no command: typo note or prompt, as before).
- `menu(line)`: first word: command names (Rust fuzzy ranking); later: children of the typed path with the typed prefix, any case, table order; none below argument text or an unknown word.
- `key(line, row, Tab|Enter)`: Tab on a row: its path, a space when it has children or expects text, its children open. Enter on a row typed in full: submit when it runs bare, else its children open. Enter on a row typed in part: complete, then descend (children), wait (text expected) or submit. No row: Tab opens the line's menu; Enter submits unless `Opens`. A row that is not a child of the typed path counts as no row.
- Lines longer than 4096 chars: no menu, Enter submits as typed; `resolve` up to the wire's string bound.
- Unknown suggestion: Rust edit distance over the children of the path (`find_slash_command_suggestion`).

Laws: `laws/command.bend` (R1-R14), proofs `proof/command/` (imported from `PROOF.bend`). Code: `eukhe-tui/src/command_paths.rs` (table, codec, calls), `autocomplete.rs` (`path_suggestions`, `slash_path_at`), `editor/autocomplete.rs` (`apply_path_key`, `ghost_hint`), `editor/input.rs` (Tab/Enter arms), `session_ui/commands.rs` (`handle_slash`: `Unknown`/`Opens`/`Runs`). Tests: `command_paths::tests`, `editor::path_key_tests`, `autocomplete::tests`.

#### Turn visibility

Working indicator: on from Enter to turn end, only while work runs (prompt traveling or queued, a turn of its run unanswered, a compaction running).

- Stays on while the reply streams: an answer still behind its pace at turn end keeps the row up, as the end left it, until the frame showing the last text.
- One clock from Enter through the run's requests, retries, compactions, re-attach.
- Chat rebuild (re-attach, worker replacement, reconnect) derives it from the snapshot and this window's prompt: traveling or queued prompt keeps it; stored answer does not raise it; compaction outside a turn shows, then ends.
- Late prompt ack never re-raises it (run ended, or session closed).

Turn ending without an answer leaves exactly one row stating it and the next step:

- the failure (with `/login`, the provider's key or `/model` for a missing key);
- the retry episode's outcome line;
- `The turn ended without a reply` (blank answer, turn the engine reported nothing for, run ended before its first request or after a tool round);
- refused or lost prompt (draft returns to editor, or wait and resend);
- closed session (reopen from Agents View).

- Lost-prompt row retires if the turn shows after all.
- Reopened chat folds the same rows from the stored transcript (`snapshot::fold_transcript` with `TurnTail`): each ended turn's end row; one line per retry episode in any storage order; a reply that streamed text before failing keeps the text, no second error.
- Window-only rows (refused or lost prompt, closed session) survive a rebuild of the same session.
- `Primary provider recovered`: a toast (no transcript records it).

Laws (draft): `LAWS.bend` section `turn_visibility`, model `bend/turn_visibility.bend`. Code: `session_ui/apply.rs` (`apply_update`), `session_ui/prompt.rs` (`apply_prompt_outcome`), `session_ui/lifecycle.rs` (`attach_session`, `rebuild_view`), `snapshot.rs` (`fold_transcript`, `reconstruct`), `snapshot/turn_end.rs`, `view.rs` (`start_loader`, `stop_loader`, `loader_row`), `view/streaming.rs` `advance_paces` (row through the reveal). Tests: `tests/turn_visibility_headless.rs` (findings' live histories), `snapshot::tests::turn_end`, `tests/failed_turn_visible_headless.rs`, `view::screen_tests::the_loader_stays_up_until_the_streamed_text_all_shows`.

### T1. Themes

One theme source for the terminal UI and HTML export (`/export`, `eukhe session export`). Crate `eukhe-theme`: theme files, validator, name resolver, color math; both surfaces call the same functions.

#### The theme file

JSON; schema `theme-schema.json` beside the bundled themes in `crates/eukhe-theme/themes/` (`eukhe`, `dark`, `light`).

- `name`: resolution name.
- `vars`: named colors. A non-color value names a variable; each reference resolved once at read. Missing variable or cycle: invalid.
- `colors`: one per token: `#rrggbb`, `""` (terminal default) or xterm-256 index 0-255. Other value, unknown token, or missing required token: invalid.
- `export`: optional `pageBg`, `cardBg`, `infoBg` for HTML export; absent: derived from `userMessageBg`.

Optional token fallbacks:

- `mdBody` → `text`.
- `background` → `export.pageBg` → `userMessageBg` → default theme's background.
- `foreground`, `refinementHeader`, `refinementSummary` → same-mode builtin (`eukhe` dark, `light` light).

Mode from background, never name: light when background WCAG relative luminance > 1/2.

HTML export: each token a CSS variable (`--<token>`), `#rrggbb`. Terminal default (`""`) paints foreground on text tokens, background on surface tokens (ending in `Bg`, and `background`). `template.css` has no own colors; reads only these variables.

#### Which theme

Setting `theme` (`/settings`); empty = `eukhe` everywhere. Name resolves by the file's `name`, in order:

1. Registered files: `themes` arrays of settings, packages, project directories, then `--theme` paths.
2. Builtin themes.
3. Files in `<agent-dir>/themes/`.

- First valid file with the name wins. Later valid same-name file with other colors: collision warning; same theme: loses silently.
- Unknown name: `eukhe` with a warning. Resolution never fails.
- Export uses the terminal UI's sources: TUI sends registered files with `/export` (`themePaths`); daemon resolves the session's resource themes when a client sends none (dashboard); `eukhe session export` reads setting `theme` and flags `--theme`, `--no-themes`.

#### Laws

`laws/theme.bend`, `laws/color.bend` (T1), model `bend/theme/`, `bend/color.bend`; proved in `proof/theme/` and `proof/color/`:

- Empty name → default theme; name → first valid theme having it; unknown name → default theme with warning.
- Loaded file is valid; a valid file's palette defines every token.
- Mode follows background; name changes neither palette nor mode.
- Each shipped theme: text tokens ≥ 4.5:1 against their background; non-text tokens (borders, rules, effort ramp ends) ≥ 3:1. User and custom message texts measured on their own surfaces. Contrast: exact integer comparison.
- Each shipped theme: status colors (accent, success, warning, error) distinct in a 256-color terminal.

Bridge test `crates/eukhe-core/src/export_html/theme_bridge.rs`: Rust and model on the same scenarios; model tables equal theme files; resolution, validation, luminance, contrast, 256-color mapping agree.

### T3. Terminal colors

Terminal UI paints only theme colors. In `eukhe-tui` only `src/theme.rs` makes colors: `theme::Color`'s value is private to it, so the compiler refuses color literals elsewhere, tests included. Other code gets colors from a `Theme`: a theme-file token or a value `theme.rs` computes from tokens. `eukhe-cli`'s exit resume hint comes from the TUI in the theme's `dim` color.

#### The tokens

- `effortLow`, `effortHigh`: effort ramp ends. A model offers a ladder of n levels (any length). Rung k (1 to n), per channel: channel's lower end + floor(d * w / n); d = channel distance; w = k if the channel rises from `effortLow` to `effortHigh`, n - k if it falls. So rung n = `effortHigh`; ramp starts one step above `effortLow`. `/model` picker: each filled effort square of the selected row has its rung.
- `contextHigh`: context usage tone between `warning` and `error`.
- `liftLight`, `liftDark`: targets a selection band moves toward when too near its surface (`liftLight` if selection lighter than surface, `liftDark` if darker). Onboarding wash lifts the background 8% toward `liftLight` (dark theme) or `liftDark` (light theme).

#### The usage bands

Status line: context usage of the daemon-served window (`contextUsage.contextWindow`). Tone: `dim` < 1/2, `warning` from 1/2, `contextHigh` from 7/10, `error` from 9/10. Band reached when window * num <= tokens * den, exactly. Unknown window (0): no band. No band is a token count: every window turns at the same share.

#### Laws

`laws/tui_color.bend`, `laws/theme.bend` (T3), model `bend/tui_color.bend` with `bend/theme/bundled.bend` theme tables; proved in `proof/tui_color/` and `proof/theme/`:

- Ramp: one rung per level. Any ladder length: each channel moves from `effortLow` toward `effortHigh`, never back. Ladder length ≤ widest channel distance of the ends: all rungs distinct. Each shipped theme: rungs distinct for any ladder of the level vocabulary.
- Each band: a window fraction in (0, 1], above the previous band. More tokens, same window: never a lower band. Band depends only on the used fraction: same fraction of a k-times window, same band.
- Every terminal UI color role resolves in every valid theme's palette and paints a color in every shipped theme.

Bridge test `crates/eukhe-tui/src/theme/bridge.rs`: Rust ramp, shipped ramps, bands, roles vs `bridge/bridge_tui_color.bend`.
