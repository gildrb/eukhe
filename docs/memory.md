# Chat memory

Source of truth: Victor Taelin's OptChat gist ("UniiChat: one chat that never ends",
[91837951](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449),
revision 2026-10-08). This page maps each gist rule to Rust code and the law or test securing it.

- Rust: `crates/eukhe-core/src/memory/`, `crates/eukhe-core/src/durable/optchat/`; paths below start at `crates/eukhe-core/src/`.
- Bend model of the pure core (view, merge order, sawtooth, compaction view, work queue): `bend/optchat.bend`.
- `LAWS.bend` states the laws; `PROOF.bend` proves them.
- Bridge test: Rust planner and Bend model run the same scenarios; output equal byte for byte.

## Use

- Store: `~/.eukhe/chat/`, one append-only log.
- Kinds: `user`, `talk`, `tool`, `echo`, `work` (subagent or background report).
- Compactor writes one-line summaries into a binary tree over the log.
- Summary target 512 bytes; longer: retried while shorter, max 5 tries; shortest cut to 512 bytes.
- Failed summary: retried at next message and every 10 s while a turn waits; 3rd failure: line = message cut to 512 bytes.
- Idle chat: no model call.
- Turn waits for view summaries max `memory.settleTimeoutMs`.
- View = context each root turn starts from. Past 128 KB, one batch merges it to 64 KB.
- View saved to `view.json` on each change: prompt cache valid across restarts.
- Cache mark on last whole block of 4 lines.
- Compaction calls: own view, 16-32 KB.

|Command|Effect|
|---|---|
|`/memory`, `/memory view`|Status and every view line|
|`/memory model`|The `/model` hub at the `memory` role: compaction model and reasoning effort (saved as `memory.model`, `memory.thinking`, default `medium`)|

- Status bar: `mem N/128K`.
- Each compactor change: a `memory:` row. Summary text at full detail only.

## Check it

```nu
bend PROOF.bend             # ALL PROOFS CHECK
bend PROOF.bend --verdict   # same, BendTT kernel (needs Lean 4.34.0)
make laws                   # both
cargo test -p eukhe-core --lib memory::chat::bridge
cargo test -p eukhe-core --lib memory::compactor::bridge
```

- `make ci-local` (local full gate, nightly gate) runs all of this; needs Bend 2.0.38, Lean 4.34.0 (pinned in `scripts/toolchain.env`).
- Bridge test skips with a message without `bend`; `EUKHE_REQUIRE_BEND=1` (set in the full gate) makes it fail.

## The Bend model

| File | Holds |
| --- | --- |
| `bend/optchat.bend` | Model: nodes, view, due, push, fit, sawtooth, compaction view, work queue. |
| `bend/spec.bend` | Law vocabulary: `Tiles`, `Merged`, `Summarized`, `Before`, `Prefix`. |
| `LAWS.bend` | Every eukhe law as open claims, one section per area. |
| `PROOF.bend` | Imports only; `proof/<area>/<law>.bend` one law's proof, `proof/<area>/base.bend` and `proof/base.bend` shared lemmas. |
| `bend/bridge.bend` | Runs the model on a scenario file; built with `bend bend/bridge.bend -o <binary>`. |
| `memory/chat/bridge.rs` | Bridge test. |

- Node index `i`: binary, lowest bit first; parent = drop lowest bit. All merge-order arithmetic on bits. Kernel numbers are unary, so this keeps bounded proofs (law d) in fuel.
- Universal proofs read bit lists by value (`Bits.val`); compare, add, shift agree with values (`proof/optchat/push_agrees_always.bend`).

Lists, not arrays:

- View: each merge reads every pair for the most due and removes one middle line; an array does the same work (full read, shift). View: ~100s of lines.
- Built nodes: binary trie per level keyed by bits of `i`; sparse, grow-only; lookup ~20 steps.
- Numbers: ~20-bit lists; fast in kernel; plain induction.
- Proofs: every universal law by induction on these lists (`push_agrees_always` inducts on view as "view one level up, then one line"). Bend 2.0.37 `Array` is a single-owner `Type`: a state holding one cannot be reused or compared in a law; indexed by wrapping `U32`; Base proves nothing about its reads/writes. An array model needs its own proven array theory and bridge, no less work per merge.

- Model = specification; Rust = production. Bridge runs the compiled model (`bend/bridge.bend` imports `bend/optchat.bend`, the module the laws speak of), so laws cover the code the bridge runs.
- Due compare without division: `(T - last_a)/2^la > (T - last_b)/2^lb` ⇔ `(T+1)·2^lb + e_b·2^la > (T+1)·2^la + e_a·2^lb`, `e = last + 1`. Rust compares `(T + 1 - first)/2^l`: same order shifted by 2; bridge shows agreement.

### The laws and their strength

Universal: every input. Bounded: computed for named inputs.

| Law | Gist | Says | Strength |
| --- | --- | --- | --- |
| `view_covers` | §3 | After any event history, view covers `0..T-1`: each once, contiguous, oldest first, each line a tree node. | Universal |
| `cview_covers` | §4 | Same for compaction view. | Universal |
| `message_appends` | §3.2 | No batch: a message appends only its line; old view is prefix of new. | Universal |
| `message_merges_nothing` | §3.2 | And merges nothing. | Universal |
| `merge_is_one_pair` | §3.1 | Merge replaces two sibling lines with their built parent, or no change. | Universal |
| `merge_covers` | §3.1 | Merge keeps coverage. | Universal |
| `push_agrees` | §3.2 | Budget = push's list length: due order makes exactly Taelin's push merges each step. | Bounded: t = 0..20,000 (gist's check) |
| `push_agrees_always` | §3.1, §3.2 | Same at every t of any number of pushes. | Universal |
| `fit_reaches_budget` | §3.2 | Batch ends at or under budget unless no pair can merge (unbuilt parents). | Universal |
| `fit_merges_built` | §3.2 | Batch merges only into built parents. | Universal |
| `view_summarized` | §3 | After any history every merged view line is built; only a message's own line waits for its summary. | Universal |
| `cview_summarized` | §4 | Same for compaction view. | Universal |
| `last_merges_8_9` | §3.2 | T = 10 (view `0+4, 4+4, 8+1, 9+1`, budget 3): due from `last` merges `8-9`, as push. | Bounded: gist's example |
| `first_merges_0_7` | §3.2 | Due from `first` merges `0-7`. | Bounded: gist's example |
| `first_is_not_last` | §3.2, §7.1 | `first` and `last` orders differ. | Bounded: gist's example |
| `first_leaves_push` | §3.2, §7.1 | Due from `first` leaves push within 11 steps. | Bounded: t = 0..10 |
| `context_ends_at_node` | §4 | Compaction view ends at its node; only built lines. | Universal |
| `context_is_prefix` | §4 | Compaction's view is a prefix of the compaction view. | Universal |

`push_agrees_always` (`proof/optchat/push_agrees_always.bend`): under push alone Taelin's list is a bijective binary counter. Keep bits `d_j` (newest first): `T = sum (1 + d_j)·2^j`; entry j = one line of level `j + d_j`. Push's list (`pa.GE`) and view (`pa.GV`) are functions of the digits; each step takes both to the next count:

- Push = digit increment: 0 absorbs, 1 carries (`pa.push_ge`).
- View lines start at push's states (`pa.same_lines`).
- Fit makes exactly the carry's merge (`pa.step`). Lowest digit 1: view = higher digits' view one level up + new line; due order between lifted lines is the same (T + 2 doubles), so step = lifted step (`pa.fit_lift`). Lowest digit 0: pair (line 0, new line) is due exactly 1; every older line ends at most `2^(l+1) - 2` messages before its view ends (`pa.Good`), so due < 1 (`pa.old_one`); later pairs cannot merge (levels differ by one). With push's length as budget this one merge is all; all digits 1: push's list grows, fit merges nothing.

- Bounded law kept: independent computed proof. `first` agrees with push at 481 of 20,001 steps, as gist says (`O.agree.count(O.First{}, 20001n)`).
- Kernel runs out of fuel on 20,001 steps, so `proof/optchat/push_agrees.bend` splits into 20 chunks of 1,000 steps + 1 step, joined by an induction lemma. Each chunk starts from a written-out state, checked by computation. Each join names remaining steps as a literal (`20001n`, `19001n`, …, `1001n`): checker compares a sum with a literal ≤ 1,000 steps deep. 20 nested sums vs `20001n` recurse 20,001 frames and overflow the checker's JavaScript stack in some runs.
- Timing (this machine): `bend PROOF.bend` ~30 s; `--verdict` ~2 min 15 s.

### What is trusted

- Laws: theorems about `bend/optchat.bend`, checked by Bend 2.0.38 and its BendTT kernel (Lean 4.34.0).
- Rust = model: finite differential test (bridge), not proof; also trusts Bend 2.0.38 compiler, runtime, clang (build the bridge binary).
- Deliberate breaks, each caught, then removed:
  - Due from `first` in model: `last_merges_8_9` and `push_agrees_always` proof fail.
  - Due without shift (`t` for `T + 1` in `more_due`), or pair levels swapped in cross comparison: `push_agrees_always` proof fails.
  - Budget push length + 1 in `agree.go`: `push_agrees_always` proof fails.
  - Merge into unbuilt parent in model (`mergeable` without built check): `fit_merges_built` proof fails.
  - Due from `first` in Rust: bridge fails.
  - Rust batch merging to ceiling, not floor: bridge fails.

### The bridge

- `memory/chat/bridge.rs`: scenarios from a fixed random seed; each event to Rust `Chat` and a scenario file; Bend binary reads the file.
- After each event both print: view, compaction view, shrinking flag, batch, work queue, work queue while a turn waits (`n=`, law `need_first`, docs/harness.md H2).
- At each batch and at end: whole rendered view (`<chat> … </chat>`), and rendered compaction view for some nodes. Compared byte for byte.
- Compactor line: own bridge (`memory/compactor/bridge.rs`, docs/harness.md H1).

Scenarios (planner compared at every T up to 4,000):

- 3,000 messages, gist sizes, compactor never late.
- 4,000 messages, small sizes (6,000/3,000 and 2,000/1,000 bytes): deep tree.
- 1,500 and 2,500 messages, late compactor: calls start/fail/end in any order; batches stop above floor, resume later.
- 24 runs with random sizes, budgets, job counts.

## The rules

Status: **matched** (code does the rule), **fixed** (code did not; a test shows the fix), **deliberate** (difference, reason given).

### §1 The log

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 1 | `main/YYYY-MM-DD.jsonl` `{i, kind, text, size, date}`, `tree/YYYY-MM-DD.jsonl` `{l, i, text, size}`, `view.json` `[l, i]` pairs. | `memory/store.rs` `Store`, `MessageRecord`, `NodeRecord`; `memory/saved.rs` `save_view`, `load_view` | `store::tests::appends_go_to_their_day_file_and_read_back_after_a_reload`, `saved::tests::a_saved_view_loads_back_unchanged` | matched (D1, D2) |
| 2 | `i` permanent id; files split by day. | `store.rs` `Store::open`, `Appender::append` | `store::tests::a_gap_in_message_ids_is_an_error` | matched |
| 3 | Kinds `user`, `tool`, `echo`, `work`. | `memory/mod.rs` `Kind`; `durable/optchat/lines.rs` | `optchat::tests::input_entries_are_logged_by_their_origin` | matched |
| 4 | Kind `unii`: agent replies. | `Kind::Eukhe` (`eukhe`; old `talk` still reads) | `memory::tests::old_talk_lines_read_as_eukhe` | renamed (D3) |
| 5 | Kind `note`: pre-chat memories. | `Kind::Note`; `memory/import.rs` `import_sessions` | `import::tests::sessions_import_oldest_first_without_repeated_pastes` | fixed |
| 6 | Append only; flush each write; never edit/delete a line. | `store.rs` `Appender::append` (one write, `fsync`) | `store::tests::a_torn_last_line_is_skipped_and_terminated` | matched |
| 7 | One process owns a chat, holding a lock. | `memory/service/client.rs` `claim` (`chat/lock` socket) | `service::tests::a_second_handle_is_a_client_and_takes_over`, `a_stale_socket_is_taken_over` | matched |
| 8 | Thoughts shown, never logged. | `optchat/lines.rs` `assistant_lines` | `optchat::tests::thoughts_are_never_logged_and_tool_output_is_clipped` | matched |
| 9 | Tool output clipped to head + tail, 30,000 characters total. | `mod.rs` `CAP`, `cap_text`; `lines.rs` `tool_result_line` | `memory::tests::cap_keeps_head_and_tail_within_the_cap`, `optchat::tests::thoughts_are_never_logged_and_tool_output_is_clipped` | matched |
| 10 | Other long text never cut: logged as consecutive messages. | `mod.rs` `split_text`; `lines.rs` `entry_lines` | `memory::tests::long_texts_split_into_messages_without_losing_anything`, `optchat::tests::long_user_texts_are_logged_as_several_messages` | matched |

### §2 The tree

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 11 | `node(0, i)` = message i in ≤ 512 bytes; `node(l, i)` merges `node(l-1, 2i)`, `node(l-1, 2i+1)`; covers 2^l messages from i·2^l; named `id+n`. | `memory/view.rs` `Part`; `mod.rs` `NODE`; `service/actor.rs` `prepare` | Laws `view_covers`, `merge_is_one_pair`; `chat::tests::zoom_opens_lines_and_messages` | matched |
| 12 | Source ≤ 512 bytes is its own node, no model call; short message stays verbatim; two short lines joined by newline. | `memory/chat.rs` `Step::input`; `actor.rs` `Actor::prepare` | `chat::tests::a_nodes_input_is_its_message_or_its_children`, `service::tests::short_messages_are_their_own_lines` | matched |
| 13 | Each node built once, logged, never rebuilt. | `actor.rs` `built`; `chat.rs` `insert_node` (leaves the queues) | Bridge (queue column); `service::tests::deleting_the_saved_view_reproduces_the_identical_view` | matched |

### §3 The view

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 14 | View: node list covering the whole chat, oldest first. | `view.rs` `View` | Laws `view_covers`, `merge_covers` | matched |
| 15 | `<chat>`, one `id+n|text` line per node, `</chat>`. | `view.rs` `View::render` | Bridge (rendered views) | matched |
| 16 | Newlines → spaces. | `view.rs` `flatten` | Bridge (each node text has a newline); `view::tests::flatten_turns_every_newline_into_one_space` (`\r\n`, `\r`) | matched |
| 17 | No dates; model calls `date(id)`. | `View::render`; `optchat/tools.rs` | `service::tests::dates_read_as_local_date_and_time` | matched |
| 18 | Only summaries, never whole messages; unsummarized: `(not summarized yet: zoom it)`. | `view.rs` `line_text`; `mod.rs` `PLACEHOLDER` | Law `view_summarized`; bridge; `view::tests::placeholders_count_until_built` | matched |
| 19 | Merge order: most due pair with built parent, `due = (T - last)/2^l`, oldest of equals; repeat. | `view.rs` `View::fit`, `more_due` | Laws `push_agrees_always`, `push_agrees`, `last_merges_8_9`, `fit_merges_built`; bridge | matched |
| 20 | Budget = push's list length: push's merges every step. | `View::fit` | Law `push_agrees_always` (universal, every t); law `push_agrees` (bounded, t ≤ 20,000) | matched |
| 21 | From `first` is wrong: T = 10 merges `0-7`, push merges `8-9`. | `View::fit` (uses `last`) | Laws `first_merges_0_7`, `first_is_not_last`, `first_leaves_push` | matched |
| 22 | New message appends its line; nothing else changes. | `chat.rs` `Chat::grow` | Laws `message_appends`, `message_merges_nothing`; bridge | matched |
| 23 | Past 128,000 bytes one batch merges most due pairs down to 64,000 bytes. | `mod.rs` `VIEW_CEILING`, `VIEW_FLOOR`; `chat.rs` `Chat::batch` | Law `fit_reaches_budget`; bridge | matched |
| 24 | Batch merges only built-parent pairs; short of 64 KB, merges what it can each new message until reached. | `Chat::grow`, `Chat::batch` (`shrinking`) | Laws `fit_merges_built`, `fit_reaches_budget`; bridge (late compactor); `chat::tests::a_restart_keeps_a_shrinking_view_shrinking` | fixed (F1) |
| 25 | Save view to `view.json`, load at start; never rebuild from log. | `actor.rs` `Actor::load`, `save_view`; `chat.rs` `Chat::from_loaded` | `chat::tests::the_view_folds_from_the_logged_merges`, `a_restart_keeps_a_shrinking_view_shrinking`; `service::tests::deleting_the_saved_view_reproduces_the_identical_view` | deliberate (D1) |
| 26 | Call input: `[tools] [system prompt] [view] [new message]`. | `optchat/request.rs` `transform`, `request_messages` | `optchat::tests::a_request_joins_the_leading_user_texts_behind_the_view` | deliberate (D11) |
| 27 | Tools and system prompt never change: no dates, no state. | `memory/prompts.rs` `memory_system_layer`; `prompts/system_prompt.rs` `environment_section` | `prompts::system_prompt::tests::chat_memory_prompt_leads_with_memory_and_ends_with_the_user_instructions` | matched (D4) |
| 28 | Between batches view grows only at end; a batch rewrites it once. | `Chat::grow` | Laws `message_appends`, `merge_is_one_pair`; bridge | matched |
| 29 | View in blocks of 4 lines; cache marks on last whole block and request end. | `mod.rs` `BLOCK`; `view.rs` `pieces`; `request.rs`; `memory/compactor.rs` `build_line` | `view::tests::pieces_end_the_marked_piece_at_the_last_whole_block`, `compactor::tests::the_view_is_marked_at_its_last_whole_block` | matched |
| 30 | Call whose marked prefix another call is writing waits until that response starts. | `service/prefix_gate.rs`; `compactor.rs` `ResponseStarted`; `actor.rs` `spawn_build` | `service::tests::a_waiting_compaction_goes_once_the_writers_response_starts`, `prefix_gate::tests::one_call_writes_a_new_prefix_and_the_others_wait_for_it` | fixed |
| 31 | No 1-hour entries, no keep-alive pings. | `memory/summarizer.rs` (no cache retention, no ping) | — (absence) | matched |

### §4 Compactions

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 32 | Compaction: turns' system prompt and tools (never called), its view, its task. | `request.rs` (sets `prompt.json`); `saved.rs` `CompactionPrompt`; `compactor.rs` `build_line` | `service::tests::compactions_reuse_the_turns_prompt_and_see_built_lines_only` | matched |
| 33 | Its view: chat view merged further to 16-32 KB, same sawtooth; merged to 16 KB once, then new lines appended; re-merged past 32 KB or when the chat view merges. | `mod.rs` `COMPACTION_CEILING`, `COMPACTION_FLOOR`; `chat.rs` `grow`, `batch`, `fit_compaction` | Laws `cview_covers`, `cview_summarized`; bridge | matched |
| 34 | Compaction view ends at the node: lines before the message, or for a merge lines up to its last message; built lines only. | `chat.rs` `Chat::context`; `view.rs` `render_built_until` | Laws `context_ends_at_node`, `context_is_prefix`; bridge | fixed (F2) |
| 35 | Task texts verbatim, with the 512-dash ruler. | `prompts.rs` `compress_task`, `merge_task`, `ruler` | `prompts::tests::tasks_carry_the_ruler_and_the_whole_input` | matched |
| 36 | Over 512 bytes: `Too long:` follow-up in the same conversation; line cut at 512 bytes. | `prompts.rs` `cut_follow_up`; `compactor.rs` `build_line` | `prompts::tests::the_cut_falls_at_the_limit_without_splitting_characters`, `compactor::tests::over_long_lines_get_the_cut_and_the_shortest_cut_wins` | matched |
| 37 | Max 5 tries; keep shortest line. | `mod.rs` `TRIES`, `cut`; `build_line` | Laws `line_calls_at_most_tries`, `line_fits`, `line_takes_first_fit`, `line_stops_when_not_shorter`, `line_empty_is_a_try`; compactor bridge; `compactor::tests::a_follow_up_not_shorter_ends_the_tries`, `a_line_at_the_limit_ends_the_retries` | deliberate (D9) |
| 38 | Failed call retried at next message. | `actor.rs` `retry_failed`, `failed` | `service::tests::a_failed_node_is_tried_again_only_for_a_waiting_turn`, `a_node_that_keeps_failing_is_built_from_its_input`; law `fail_cap_builds` | matched (D5) |
| 39 | Max 8 concurrent calls. | `mod.rs` `JOBS`; `chat.rs` `Chat::candidates` | Bridge (queue column, 1 to 8 jobs) | matched |
| 40 | Message node starts once < 8 lines before it are unbuilt; merge starts once both halves built. | `Chat::candidates`, `note_ready_parent` | Bridge (queue columns); law `need_first` | matched (D5) |
| 41 | Compaction view stops at first unbuilt line. | `view.rs` `render_built_until` | Law `context_ends_at_node`; bridge | matched |
| 42 | Ready nodes in queues; never scan the tree for work. | `chat.rs` `ready` (queue, filled on build) | Bridge (queue order); code review: `candidates` reads only view lines and queue | matched |
| 43 | Model: a cheap one. | `summarizer.rs` `configured_memory_model` | `summarizer::tests` | deliberate (D6) |

### §5 The prompt

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 44 | One system prompt for turns and compactions; user instructions follow. | `prompts.rs` `memory_system_layer`; `prompts/system_prompt.rs` | `prompts::system_prompt::tests::chat_memory_prompt_leads_with_memory_and_ends_with_the_user_instructions` | matched (D4) |
| 45 | Prompt verbatim, Unii renamed; computers paragraph dropped without device tools. | `prompts.rs` `INTRO`, `VIEW_DOC`, `TURNS`, `COMPACTIONS`; gist text in `memory/prompts/gist_prompt.txt` | `prompts::tests::the_system_prompt_is_the_specs_with_only_the_documented_deviations` | fixed (F3) |

### §6 A turn

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 46 | Call running: hand m to it between tool calls; log as `user`. | Harness steering; `lines.rs` `user_input_line` | `optchat::tests::a_message_sent_during_a_call_joins_it_between_tool_calls` | matched |
| 47 | Else wait until every message before m is summarized; call in a fresh session. | `request.rs` `transform`, `pin`; `actor.rs` view waiters (`settled_render`), `deadline_view` | `service::tests::a_settled_view_never_shows_a_placeholder_while_another_client_appends`, `a_turn_gets_the_view_by_its_deadline_when_the_model_never_answers`; laws `settle_reached`, `need_first` | deliberate (D10) |
| 48 | Log each reply, tool call, result as it happens. | `optchat/logger.rs` | `optchat::tests::a_crash_between_append_and_cursor_logs_no_line_twice` | matched |
| 49 | Render view before logging the new message; message goes whole after it. | `logger.rs` `log_conversation`; `request.rs` | `optchat::tests::a_run_sends_the_pinned_view_and_its_own_messages_and_logs_them` | deliberate (D11) |
| 50 | Nothing carries over between turns. | `request.rs` `request_messages` | Same test | matched |
| 51 | Per-turn state after the view, never in system prompt. | `request.rs` `request_messages` | `optchat::tests::a_request_joins_the_leading_user_texts_behind_the_view` | matched |
| 52 | `zoom(id, n)`: description verbatim; `n` power of 2, `id` multiple of `n`. | `prompts.rs` `ZOOM_TOOL_DESCRIPTION`; `chat.rs` `Chat::zoom`; `optchat/tools.rs` | `chat::tests::zoom_opens_lines_and_messages`, `optchat::tests::zoom_and_date_keep_their_schemas_and_read_the_chat` | matched |
| 53 | `zoom(id, 1)`: whole message with images. | `saved.rs` `save_images`, `load_images` (`chat/images/`); `actor.rs` `zoom`; `tools.rs` `zoom_result` | `service::tests::a_message_zoomed_whole_comes_with_its_images`, `optchat::tests::the_zoom_tool_gives_a_message_with_its_images` | fixed |
| 54 | `zoom("Name")`: agent's whole chat; its steps stay in its own log. | `tools.rs` `agent_chat`; `lines.rs` `chat_text` | `optchat::tests::zoom_by_name_gives_an_agents_whole_chat` | fixed |
| 55 | Long message comes in pages. | Rule 10: each page one message. | `optchat::tests::long_user_texts_are_logged_as_several_messages` | matched |
| 56 | `date(id)`: description verbatim. | `prompts.rs` `DATE_TOOL_DESCRIPTION`; `tools.rs` | `service::tests::dates_read_as_local_date_and_time` | matched |
| 57 | Subagent: fresh call, view then task. | `request.rs` (`MemoryRole::Subagent`); `prompts.rs` `subagent_system_layer` | `optchat::tests::a_subagent_pins_one_view_for_its_conversation_and_logs_nothing` | matched |
| 58 | Final reply returns as one `work` message, `[Name] report`; master never waits or polls. | `lines.rs` `report_line`; prompt's `TURNS` | `optchat::tests::agent_replies_are_logged_as_work_and_owed_rows_are_not` | matched |

### §7 Mistakes to avoid

| # | Mistake | Avoided by | Secured by |
| --- | --- | --- | --- |
| 59 | 1. Age from pair's first message. | Rule 19 (`last`) | Laws `first_is_not_last`, `first_leaves_push`, `push_agrees_always` |
| 60 | 2. Merging every message. | Rules 22-24 | Laws `message_appends`, `fit_reaches_budget`; bridge |
| 61 | 3. Rebuilding view per turn or at restart. | Rule 25 | `chat::tests::a_restart_keeps_a_shrinking_view_shrinking` |
| 62 | 4. K lines per level. | Rule 23 (byte budget) | Law `fit_reaches_budget` |
| 63 | 5. Whole messages in view, or start of an unsummarized one. | Rules 18, 41 | Laws `view_summarized`, `context_ends_at_node` |
| 64 | 6. Compaction without context, or with own system prompt. | Rules 32-34 | Rule 32-34 tests and laws |
| 65 | 7. Trusting the model to count bytes. | Rules 35-37 | Rule 35-37 tests |
| 66 | 8. Lines under 512 bytes. | `NODE = 512` | `chat::tests::free_nodes_need_no_model` |
| 67 | 9. Logging thoughts. | Rule 8 | Rule 8 test |
| 68 | 10. Dates or state in system prompt or tools. | Rules 27, 51 | Rule 27, 51 tests |
| 69 | 11. Carrying a conversation across turns. | Rule 50 | Rule 50 test |
| 70 | 12. Two writers on one log, or unflushed writes. | Rules 6, 7 | Rule 6, 7 tests |
| 71 | 13. Scanning the tree for work. | Rule 42 | Bridge |

## Fixes

- **F1.** Batch stopped above 64 KB continued at next messages, but a restart lost that state (view only appended until 128 KB again; differed from live). Now: batch runs every message while shrinking; each batch writes a `tree/` line, also when merging nothing: `{merge, open, t}` (`open`: view above floor; `t`: message count). Restart reads `open` from last line. Old lines without `open`/`t` load with `open` false.
- **F2.** Compaction view took lines starting before the node; now lines ending at or before it (gist: "the lines before the message, or for a merge the lines up to the merge's last message"). With the tree as built both give the same lines (a line crossing the node's end contains the unbuilt node); bridge shows it.
- **F3.** Prompt said "Spawn subagents when needed"; gist: "Do the user's tasks yourself, with your tools, … Use subagents only when the user asks for them." Kind list lacked `note`; tool list lacked images for `zoom(id, 1)` and `zoom("Name")`.

## Deliberate differences

- **D1. View folded from logged merges.** `view.json` written after every change; at start the view is folded from messages and `tree/` merge lines and checked against `view.json`. Fold replays the live view's exact merges in order: same parts, same bytes; no recompute by another rule (gist's warning). Merge lines append-only; `view.json` replaced per change, can be lost in a crash; lost/stale `view.json` gives the same view (`service::tests::deleting_the_saved_view_reproduces_the_identical_view`). Pre-merge-line chat imports its `view.json` once, as merges.
- **D2. Extra fields.** Message line may carry `key` (idempotent append across crashes). `tree/` also holds merge lines (D1). All gist fields unchanged.
- **D3. `eukhe`, not `unii`.** Gist: rename Unii to the agent's name; replies are kind `eukhe`, prompt's kind list says `eukhe`. Pre-rename `talk` lines read as `eukhe`; old tree lines keep `talk:` text (nodes never rebuilt).
- **D4. Static layers.** eukhe's static tool notes sit between memory prompt and user instructions; unchanging, so cache prefix holds. Working directory: fixed per session set-up, unchanged across a chat's sessions.
- **D5. Waiting turn first.** While a turn waits (rule 47) only the view's unbuilt lines start; ready merges wait for settle; calls for other nodes stop when the wait starts (no failure; laws `need_first`, `need_first_running`). Failed node also retried every 10 s (`RETRY`), else a turn waits for a message that never comes. 3rd failed call builds the node from its input cut to 512 bytes (`FAILURES`, law `fail_cap_builds`): view settles after bounded compactor outcomes (laws `settle_*`, docs/harness.md H2). Wait never errors.
- **D6. Model.** Gist: Claude Haiku. eukhe: `memory.model`, else auxiliary model.
- **D7. Compaction view at start.** Not logged; at start = view merged to 16 KB once, as gist. Affects only which prefix first compactions read from cache.
- **D8. Crash between message and batch line.** Shrinking: every message writes a batch line; restart sees the gap and runs the batch. Not shrinking and a message passes 128 KB: crash can lose the batch line; batch runs at next message. Restart never runs a batch alone (live chat also waits for next message).
- **D9. Lines cut, not trusted to shrink.** Gist keeps shortest of 5 tries at any length. eukhe:
  - stops at a follow-up not shorter than best (measured local model repeated a 1,300-byte line);
  - empty or thinking-only reply = last try (measured model thought 12,000 tokens, wrote nothing);
  - cuts best line, else input, to 512 bytes at a character boundary.

  Every line 1-512 bytes (docs/harness.md H1). Model call past 10 min fails (`CALL_DEADLINE`).
- **D10. Turn waits for its view max `memory.settleTimeoutMs`.** Gist waits until every prior message is summarized. After `memory.settleTimeoutMs` (default 20 s) the turn takes the view as is: each unsummarized line shows its input (labeled message) cut to 512 bytes; never placeholder, never error. Summarized later; next turn sees it (docs/harness.md H2.3).
- **D11. Turn marked "Turn:".** Gist marks compactions "Compaction:" and leaves turns unmarked; one model took a bare user message for compaction input and replied with a summary line. eukhe prepends `Turn: the new message follows. Answer it as Eukhe, with your tools; do not summarize it.`; prompt opening names both marks (`memory/prompts.rs` `INTRO`, `TURN_TASK`). Model-only; chat logs the user's words alone. Subagent's first message: no mark (task follows view).
