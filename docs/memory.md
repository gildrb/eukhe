# Chat memory

eukhe's chat memory is Victor Taelin's OptChat design ("UniiChat: one chat
that never ends", gist
[91837951](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449),
revision of 2026-10-08). The gist is the only source of truth. This page
lists every rule of the gist, the Rust code that does it, and the law or the
test that secures it.

- The Rust code is in `crates/eukhe-core/src/memory/` and
  `crates/eukhe-core/src/durable/optchat/`. Paths below start at
  `crates/eukhe-core/src/`.
- The pure core (the view, the merge order, the sawtooth, the compaction
  view, the work queue) has a model in Bend: `bend/optchat.bend`.
- `LAWS.bend` states what the model must do. `PROOF.bend` proves it.
- The bridge test runs the Rust planner and the Bend model on the same
  scenarios. The two must print the same output, byte for byte.

## Check it

```nu
bend PROOF.bend             # ALL PROOFS CHECK
bend PROOF.bend --verdict   # the same, with the BendTT kernel (needs Lean 4.34.0)
make laws                   # both
cargo test -p eukhe-core --lib memory::chat::bridge
```

CI does all of this (`.github/workflows/ci.yml`, job `laws`, and the test
shards). `scripts/install_bend.sh` installs Bend 2.0.37 and Lean 4.34.0
from their releases and checks each download against its sha256. The
bridge test skips with a message when `bend` is not installed. In CI,
`EUKHE_REQUIRE_BEND=1` makes a missing `bend` fail the test.

## The Bend model

| File | What it holds |
| --- | --- |
| `bend/optchat.bend` | The model: nodes, the view, due, push, fit, the sawtooth, the compaction view, the work queue. |
| `bend/spec.bend` | What the laws speak of: `Tiles`, `Merged`, `Summarized`, `Before`, `Prefix`. |
| `LAWS.bend` | The laws, as open claims. |
| `PROOF.bend` | One proof per law. It imports `bend/proof_*.bend`. |
| `bend/bridge.bend` | Runs the model on a scenario file. The bridge test builds it with `bend bend/bridge.bend -o <binary>`. |
| `memory/chat/bridge.rs` | The bridge test. |

The model keeps a node's index `i` in binary, lowest bit first. So the
parent of a node is one step away: drop the lowest bit. All arithmetic of the
merge order runs on these bits. The proof kernel has unary numbers, so this
keeps the bounded proofs (law d) inside its fuel.

The model uses lists, not arrays, and says why:

- The view: each merge reads every pair to find the most due one, and
  removes one line from the middle. An array does the same work (a full
  read and a shift). The view has some hundred lines.
- The built nodes: a binary trie per level, keyed by the bits of `i`. It
  is a sparse map that only grows; lookups take about 20 steps.
- Numbers in binary: a list of about 20 bits. The kernel checks these
  fast, and the proofs use plain induction on them.

The model is a specification, not the production code. The Rust code is
the production code. The bridge test runs the compiled model
(`bend/bridge.bend` imports `bend/optchat.bend`, the module the laws speak
of), so the laws are about the code that the bridge runs.

The model compares dues without division. For two pairs `a` and `b`,
`(T - last_a)/2^la > (T - last_b)/2^lb` is the same as
`(T+1)·2^lb + e_b·2^la > (T+1)·2^la + e_a·2^lb`, with `e = last + 1`. The
Rust code compares `(T + 1 - first)/2^l`, the same order shifted by 2. The
bridge test shows that the two orders agree.

### The laws and their strength

"Universal" means: proven for every input. "Bounded" means: proven by
computation for the inputs named.

| Law | Gist | Says | Strength |
| --- | --- | --- | --- |
| `view_covers` | §3 | After any history of events, the view covers messages `0..T-1`: each once, contiguous, oldest first, each line a tree node. | Universal |
| `cview_covers` | §4 | The same for the compaction view. | Universal |
| `message_appends` | §3.2 | When no batch runs, a message appends only its own line. The old view is a prefix of the new one. | Universal |
| `message_merges_nothing` | §3.2 | And it merges nothing. | Universal |
| `merge_is_one_pair` | §3.1 | A merge replaces two sibling lines with their built parent, or changes nothing. | Universal |
| `merge_covers` | §3.1 | A merge keeps the coverage. | Universal |
| `push_agrees` | §3.2 | With push's list length as the budget, the due order makes exactly the merges of Taelin's push, at every step. | Bounded: t = 0..20,000 (the gist's own check) |
| `fit_reaches_budget` | §3.2 | A batch ends at or under its budget, unless no pair can merge (unbuilt parents). | Universal |
| `fit_merges_built` | §3.2 | A batch merges only into built parents. | Universal |
| `view_summarized` | §3 | After any history, every merged line of the view is built. Only a message's own line can wait for its summary. | Universal |
| `cview_summarized` | §4 | The same for the compaction view. | Universal |
| `last_merges_8_9` | §3.2 | At T = 10 (view `0+4, 4+4, 8+1, 9+1`, budget 3) due from `last` merges `8-9`, as push does. | Bounded: the gist's example |
| `first_merges_0_7` | §3.2 | Due from `first` merges `0-7`. | Bounded: the gist's example |
| `first_is_not_last` | §3.2, §7.1 | So `first` and `last` are not the same order. | Bounded: the gist's example |
| `first_leaves_push` | §3.2, §7.1 | Due from `first` leaves push within 11 steps. | Bounded: t = 0..10 |
| `context_ends_at_node` | §4 | A compaction's view ends at its node, and has only built lines. | Universal |
| `context_is_prefix` | §4 | A compaction's view is the start of the compaction view. | Universal |

A universal proof of `push_agrees` needs a closed form of push's list and
of the view for every T, and a comparison of every pair's due. That proof
is not done. The law holds for t = 0..20,000, the range the gist checked. The
model also counts the steps where `first` agrees with push: 481 of 20,001,
as the gist says (`O.agree.count(O.First{}, 20001n)`).

The kernel cannot run 20,001 steps in one check (it runs out of fuel), so
`bend/proof_push.bend` cuts the run into 20 chunks of 1,000 steps and one
step. A lemma proven by induction joins the chunks. Each chunk starts from
a written-out state and is checked by computation. On this machine
`bend PROOF.bend` takes about 32 s and `--verdict` about 2 min 20 s.

### What is trusted

- The laws are theorems about `bend/optchat.bend`, checked by Bend 2.0.37
  and by its BendTT kernel (Lean 4.34.0).
- That the Rust planner does the same is a finite differential test (the
  bridge), not a proof. It also trusts the Bend 2.0.37 compiler, its
  runtime, and clang, which build the bridge binary.
- The bridge and the laws catch real mistakes. Each of these breaks was
  made on purpose and then removed:
  - Due from `first` in the model: `last_merges_8_9` fails.
  - Merging into an unbuilt parent in the model (`mergeable` without the
    built check): the proof of `fit_merges_built` fails.
  - Due from `first` in the Rust code: the bridge fails.
  - A Rust batch that merges down to the ceiling instead of the floor:
    the bridge fails.

### The bridge

`memory/chat/bridge.rs` makes scenarios with a fixed random seed. Each
event goes to the Rust `Chat` and into a scenario file. The Bend binary
reads the file. After each event, both print the view, the compaction view,
the shrinking flag, the batch, and the work queue. At each batch and at the
end, both print the whole rendered view (`<chat> … </chat>`), and for some
nodes the rendered compaction view. The test compares the two outputs byte
for byte.

The scenarios:

- 3,000 messages at the gist's sizes, with a compactor that is never late.
- 4,000 messages at small sizes (6,000/3,000 and 2,000/1,000 bytes), so
  that the tree gets deep.
- 1,500 and 2,500 messages with a late compactor: calls start, fail and
  end in any order, so batches stop above the floor and go on later.
- 24 more runs with random sizes, budgets and job counts.

So the planner is compared at every T up to 4,000.

## The rules

Status: **matched** (the code does the rule), **fixed** (the code did not
do the rule; a test now shows the fix), **deliberate** (a difference, with
the reason).

### §1 The log

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 1 | `main/YYYY-MM-DD.jsonl` `{i, kind, text, size, date}`, `tree/YYYY-MM-DD.jsonl` `{l, i, text, size}`, `view.json` `[l, i]` pairs. | `memory/store.rs` `Store`, `MessageRecord`, `NodeRecord`; `memory/saved.rs` `save_view`, `load_view` | `store::tests::appends_go_to_their_day_file_and_read_back_after_a_reload`, `saved::tests::a_saved_view_loads_back_unchanged` | matched (see D1, D2) |
| 2 | `i` is the permanent id. Files split by day. | `store.rs` `Store::open`, `Appender::append` | `store::tests::a_gap_in_message_ids_is_an_error` | matched |
| 3 | Kinds `user`, `tool`, `echo`, `work`. | `memory/mod.rs` `Kind`; `durable/optchat/lines.rs` | `optchat::tests::input_entries_are_logged_by_their_origin` | matched |
| 4 | Kind `unii`: the agent's replies. | `Kind::Eukhe` (`eukhe`; old logs' `talk` still reads) | `memory::tests::old_talk_lines_read_as_eukhe` | renamed (D3) |
| 5 | Kind `note`: memories from before the chat. | `Kind::Note`; `memory/import.rs` `import_sessions` | `import::tests::sessions_import_oldest_first_without_repeated_pastes` | fixed |
| 6 | Only append. Flush each write. Never edit or delete a line. | `store.rs` `Appender::append` (one write, `fsync`) | `store::tests::a_torn_last_line_is_skipped_and_terminated` | matched |
| 7 | One process owns a chat. It holds a lock. | `memory/service/client.rs` `claim` (`chat/lock` socket) | `service::tests::a_second_handle_is_a_client_and_takes_over`, `a_stale_socket_is_taken_over` | matched |
| 8 | Thoughts are shown, never logged. | `optchat/lines.rs` `assistant_lines` | `optchat::tests::thoughts_are_never_logged_and_tool_output_is_clipped` | matched |
| 9 | A tool's output is clipped to head and tail, 30,000 characters in all. | `mod.rs` `CAP`, `cap_text`; `lines.rs` `tool_result_line` | `memory::tests::cap_keeps_head_and_tail_within_the_cap`, `optchat::tests::thoughts_are_never_logged_and_tool_output_is_clipped` | matched |
| 10 | Other long text is never cut: it is logged as several messages in a row. | `mod.rs` `split_text`; `lines.rs` `entry_lines` | `memory::tests::long_texts_split_into_messages_without_losing_anything`, `optchat::tests::long_user_texts_are_logged_as_several_messages` | matched |

### §2 The tree

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 11 | `node(0, i)` is message i in at most 512 bytes; `node(l, i)` merges `node(l-1, 2i)` and `node(l-1, 2i+1)`. It covers the 2^l messages from i·2^l and is named `id+n`. | `memory/view.rs` `Part`; `mod.rs` `NODE`; `service/actor.rs` `prepare` | Laws `view_covers`, `merge_is_one_pair`; `chat::tests::zoom_opens_lines_and_messages` | matched |
| 12 | A source that fits in 512 bytes is its own node, with no model call. A short message stays word for word. Two short lines are joined by a newline. | `memory/chat.rs` `free_text`; `actor.rs` `Prepared::Free` | `chat::tests::free_nodes_need_no_model`, `service::tests::short_messages_are_their_own_lines` | matched |
| 13 | Each node is built once, logged, never built again. | `actor.rs` `built`; `chat.rs` `insert_node` (leaves the queues) | Bridge (the queue column); `service::tests::deleting_the_saved_view_reproduces_the_identical_view` | matched |

### §3 The view

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 14 | The view is a list of nodes that covers the whole chat, oldest first. | `view.rs` `View` | Laws `view_covers`, `merge_covers` | matched |
| 15 | `<chat>`, one `id+n|text` line per node, `</chat>`. | `view.rs` `View::render` | Bridge (the rendered views) | matched |
| 16 | Newlines turned into spaces. | `view.rs` `flatten` | Bridge (each node text has a newline); `view::tests::flatten_turns_every_newline_into_one_space` (`\r\n`, `\r`) | matched |
| 17 | No dates: the model calls `date(id)`. | `View::render`; `optchat/tools.rs` | `service::tests::dates_read_as_local_date_and_time` | matched |
| 18 | Only summaries, never a whole message. A message not summarized yet shows as `(not summarized yet: zoom it)`. | `view.rs` `line_text`; `mod.rs` `PLACEHOLDER` | Law `view_summarized`; bridge; `view::tests::placeholders_count_until_built` | matched |
| 19 | The merge order: the most due pair whose parent is built, `due = (T - last)/2^l`, oldest of equal pairs; repeat. | `view.rs` `View::fit`, `more_due` | Laws `push_agrees`, `last_merges_8_9`, `fit_merges_built`; bridge | matched |
| 20 | With push's list length as budget, it makes push's merges at every step. | `View::fit` | Law `push_agrees` (bounded, t ≤ 20,000) | matched |
| 21 | Measuring from `first` is wrong: at T = 10 it merges `0-7`, push merges `8-9`. | `View::fit` (uses `last`) | Laws `first_merges_0_7`, `first_is_not_last`, `first_leaves_push` | matched |
| 22 | Each new message appends its line. Nothing else changes. | `chat.rs` `Chat::grow` | Laws `message_appends`, `message_merges_nothing`; bridge | matched |
| 23 | Past 128,000 bytes, one batch merges the most due pairs down to 64,000 bytes. | `mod.rs` `VIEW_CEILING`, `VIEW_FLOOR`; `chat.rs` `Chat::batch` | Law `fit_reaches_budget`; bridge | matched |
| 24 | A batch merges only pairs whose parent is built. If it cannot reach 64 KB yet, it merges what it can at each new message until it does. | `Chat::grow`, `Chat::batch` (`shrinking`) | Laws `fit_merges_built`, `fit_reaches_budget`; bridge (late compactor); `chat::tests::a_restart_keeps_a_shrinking_view_shrinking` | fixed (F1) |
| 25 | Save the view to `view.json`, load it at start. Never rebuild it from the log. | `actor.rs` `Actor::load`, `save_view`; `chat.rs` `Chat::from_loaded` | `chat::tests::the_view_folds_from_the_logged_merges`, `a_restart_keeps_a_shrinking_view_shrinking`; `service::tests::deleting_the_saved_view_reproduces_the_identical_view` | deliberate (D1) |
| 26 | A call's input is `[tools] [system prompt] [view] [new message]`. | `optchat/request.rs` `transform`, `request_messages` | `optchat::tests::a_request_joins_the_leading_user_texts_behind_the_view` | matched |
| 27 | Tools and system prompt never change: no dates, no state. | `memory/prompts.rs` `memory_system_layer`; `prompts/system_prompt.rs` `environment_section` | `prompts::system_prompt::tests::chat_memory_prompt_leads_with_memory_and_ends_with_the_user_instructions` | matched (D4) |
| 28 | Between batches the view only grows at its end. A batch rewrites it once. | `Chat::grow` | Laws `message_appends`, `merge_is_one_pair`; bridge | matched |
| 29 | The view goes in blocks of 4 lines. One cache mark on the last whole block, one on the request's end. | `mod.rs` `BLOCK`; `view.rs` `pieces`; `request.rs`; `memory/compactor.rs` `build_line` | `view::tests::pieces_end_the_marked_piece_at_the_last_whole_block`, `compactor::tests::the_view_is_marked_at_its_last_whole_block` | matched |
| 30 | A call whose marked prefix another call is writing waits until that call's response starts. | `service/prefix_gate.rs`; `compactor.rs` `ResponseStarted`; `actor.rs` `spawn_build` | `service::tests::a_waiting_compaction_goes_once_the_writers_response_starts`, `prefix_gate::tests::one_call_writes_a_new_prefix_and_the_others_wait_for_it` | fixed |
| 31 | No 1-hour entries, no keep-alive pings. | `memory/summarizer.rs` (no cache retention set, no ping) | — (an absence) | matched |

### §4 Compactions

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 32 | A compaction is a call with the turns' system prompt and tools (never called), then its view, then its task. | `request.rs` (sets `prompt.json`); `saved.rs` `CompactionPrompt`; `compactor.rs` `build_line` | `service::tests::compactions_reuse_the_turns_prompt_and_see_built_lines_only` | matched |
| 33 | Its view: the chat's view merged further to 16-32 KB with the same sawtooth; merged down to 16 KB once, then the new lines appended; merged again past 32 KB or when the chat's view merges. | `mod.rs` `COMPACTION_CEILING`, `COMPACTION_FLOOR`; `chat.rs` `grow`, `batch`, `fit_compaction` | Laws `cview_covers`, `cview_summarized`; bridge | matched |
| 34 | The compaction view ends at the node: the lines before the message, or for a merge the lines up to its last message. Only built lines. | `chat.rs` `Chat::context`; `view.rs` `render_built_until` | Laws `context_ends_at_node`, `context_is_prefix`; bridge | fixed (F2) |
| 35 | The task texts, verbatim, with the 512-dash ruler. | `prompts.rs` `compress_task`, `merge_task`, `ruler` | `prompts::tests::tasks_carry_the_ruler_and_the_whole_input` | matched |
| 36 | Over 512 bytes: the `Too long:` follow-up in the same conversation, with the line cut at 512 bytes. | `prompts.rs` `cut_follow_up`; `compactor.rs` `build_line` | `prompts::tests::the_cut_falls_at_the_limit_without_splitting_characters`, `compactor::tests::over_long_lines_get_the_cut_and_the_shortest_of_five_wins` | matched |
| 37 | At most 5 tries; keep the shortest line. | `mod.rs` `TRIES`; `build_line` | `compactor::tests::over_long_lines_get_the_cut_and_the_shortest_of_five_wins`, `a_line_at_the_limit_ends_the_retries` | matched |
| 38 | A failed call is tried again at the next message. | `actor.rs` `retry_failed` | `service::tests::a_failed_node_is_tried_again_only_for_a_waiting_turn` | matched (D5) |
| 39 | Up to 8 calls at once. | `mod.rs` `JOBS`; `chat.rs` `Chat::candidates` | Bridge (the queue column, with 1 to 8 jobs) | matched |
| 40 | A message's node starts once fewer than 8 lines before it are unbuilt. A merge starts once both halves are built. | `Chat::candidates`, `note_ready_parent` | Bridge (the queue column) | matched |
| 41 | A compaction's view stops at the first unbuilt line. | `view.rs` `render_built_until` | Law `context_ends_at_node`; bridge | matched |
| 42 | Keep ready nodes in queues. Never scan the tree for work. | `chat.rs` `ready` (a queue, filled when a node is built) | Bridge (the queue order); code review: `candidates` reads the view's lines and the queue only | matched |
| 43 | The model: a cheap one. | `summarizer.rs` `configured_memory_model` | `summarizer::tests` | deliberate (D6) |

### §5 The prompt

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 44 | One system prompt for turns and compactions. The user's instructions follow it. | `prompts.rs` `memory_system_layer`; `prompts/system_prompt.rs` | `prompts::system_prompt::tests::chat_memory_prompt_leads_with_memory_and_ends_with_the_user_instructions` | matched (D4) |
| 45 | The prompt verbatim, Unii renamed. The paragraph on computers is dropped when the agent has no device tools. | `prompts.rs` `INTRO`, `VIEW_DOC`, `TURNS`, `COMPACTIONS`; the gist's text in `memory/prompts/gist_prompt.txt` | `prompts::tests::the_system_prompt_is_the_specs_with_only_the_documented_deviations` | fixed (F3) |

### §6 A turn

| # | Rule | Code | Secured by | Status |
| --- | --- | --- | --- | --- |
| 46 | If a call is running, hand m to it between tool calls and log it as `user`. | Harness steering; `lines.rs` `user_input_line` | `optchat::tests::a_message_sent_during_a_call_joins_it_between_tool_calls` | matched |
| 47 | Else wait until every message before m is summarized, then call in a fresh session. | `request.rs` `transform`, `pin`; `actor.rs` view waiters (`settled_render`) | `service::tests::a_settled_view_never_shows_a_placeholder_while_another_client_appends` | matched |
| 48 | Log each reply, tool call and result as it happens. | `optchat/logger.rs` | `optchat::tests::a_crash_between_append_and_cursor_logs_no_line_twice` | matched |
| 49 | Render the view before logging the new message. The message goes whole after it. | `logger.rs` `log_conversation`; `request.rs` | `optchat::tests::a_run_sends_the_pinned_view_and_its_own_messages_and_logs_them` | matched |
| 50 | Nothing carries over between turns. | `request.rs` `request_messages` | Same test | matched |
| 51 | Per-turn state goes after the view, never in the system prompt. | `request.rs` `request_messages` | `optchat::tests::a_request_joins_the_leading_user_texts_behind_the_view` | matched |
| 52 | `zoom(id, n)`: the description verbatim; `n` a power of 2, `id` a multiple of `n`. | `prompts.rs` `ZOOM_TOOL_DESCRIPTION`; `chat.rs` `Chat::zoom`; `optchat/tools.rs` | `chat::tests::zoom_opens_lines_and_messages`, `optchat::tests::zoom_and_date_keep_their_schemas_and_read_the_chat` | matched |
| 53 | `zoom(id, 1)` gives the message whole, with its images. | `saved.rs` `save_images`, `load_images` (`chat/images/`); `actor.rs` `zoom`; `tools.rs` `zoom_result` | `service::tests::a_message_zoomed_whole_comes_with_its_images`, `optchat::tests::the_zoom_tool_gives_a_message_with_its_images` | fixed |
| 54 | `zoom("Name")` gives an agent's whole chat; its steps stay in its own log. | `tools.rs` `agent_chat`; `lines.rs` `chat_text` | `optchat::tests::zoom_by_name_gives_an_agents_whole_chat` | fixed |
| 55 | A long message comes in pages. | Rule 10: each page is one message. | `optchat::tests::long_user_texts_are_logged_as_several_messages` | matched |
| 56 | `date(id)`: the description verbatim. | `prompts.rs` `DATE_TOOL_DESCRIPTION`; `tools.rs` | `service::tests::dates_read_as_local_date_and_time` | matched |
| 57 | A subagent is a fresh call: the view, then its task. | `request.rs` (`MemoryRole::Subagent`); `prompts.rs` `subagent_system_layer` | `optchat::tests::a_subagent_pins_one_view_for_its_conversation_and_logs_nothing` | matched |
| 58 | Its final reply comes back as one `work` message, `[Name] report`. The master never waits or polls. | `lines.rs` `report_line`; the prompt's `TURNS` | `optchat::tests::agent_replies_are_logged_as_work_and_owed_rows_are_not` | matched |

### §7 Mistakes to avoid

| # | Mistake | Avoided by | Secured by |
| --- | --- | --- | --- |
| 59 | 1. Age from a pair's first message. | Rule 19 (`last`) | Laws `first_is_not_last`, `push_agrees` |
| 60 | 2. Merging at every message. | Rules 22-24 | Laws `message_appends`, `fit_reaches_budget`; bridge |
| 61 | 3. Rebuilding the view per turn or at a restart. | Rule 25 | `chat::tests::a_restart_keeps_a_shrinking_view_shrinking` |
| 62 | 4. K lines per level. | Rule 23 (a byte budget) | Law `fit_reaches_budget` |
| 63 | 5. Whole messages in the view, or the start of an unsummarized one. | Rules 18, 41 | Laws `view_summarized`, `context_ends_at_node` |
| 64 | 6. A compaction without context, or with its own system prompt. | Rules 32-34 | Rule 32-34 tests and laws |
| 65 | 7. Trusting the model to count bytes. | Rules 35-37 | Rule 35-37 tests |
| 66 | 8. Lines under 512 bytes. | `NODE = 512` | `chat::tests::free_nodes_need_no_model` |
| 67 | 9. Logging thoughts. | Rule 8 | Rule 8 test |
| 68 | 10. Dates or state in the system prompt or tools. | Rules 27, 51 | Rule 27, 51 tests |
| 69 | 11. Carrying a conversation across turns. | Rule 50 | Rule 50 test |
| 70 | 12. Two writers on one log, or writes without a flush. | Rules 6, 7 | Rule 6, 7 tests |
| 71 | 13. Scanning the tree for work. | Rule 42 | Bridge |

## Fixes

- **F1.** A batch that stopped above 64 KB went on at the next messages,
  but a restart lost that state. The view then only appended until it
  passed 128 KB again, so it differed from the live view. Now a batch runs
  at every message while the view is shrinking, and each batch writes its
  `tree/` line, also when it merges nothing: `{merge, open, t}`. `open` says
  the view is still above its floor; `t` is the number of messages. A
  restart reads `open` from the last line. Old lines have no `open` and no
  `t`, and still load (`open` false).
- **F2.** A compaction's view took the lines that start before the node.
  It now takes the lines that end at or before the node (gist: "the lines
  before the message, or for a merge the lines up to the merge's last
  message"). With the tree as it is built, both give the same lines (a
  line that crosses the node's end would contain the unbuilt node). The
  bridge shows this.
- **F3.** The prompt said "Spawn subagents when needed". The gist says "Do
  the user's tasks yourself, with your tools, … Use subagents only when the
  user asks for them." The kind list had no `note`. The tool list had no
  images for `zoom(id, 1)` and no `zoom("Name")`.

## Deliberate differences

- **D1. The view is folded from logged merges.** The gist saves the view
  to `view.json` and loads it. eukhe also writes `view.json` after every
  change, but at start it folds the view from the messages and the merge
  lines in `tree/`, and checks `view.json` against the fold. The fold
  replays the exact merges of the live view, in their order. So it gives
  the same parts, and the same bytes, as the live view. It does not compute
  the view again by another rule, which is what the gist warns against. The
  merge lines are append-only, as the log is; `view.json` is replaced on
  each change and can be lost in a crash. A lost or stale `view.json` gives
  the same view (`service::tests::deleting_the_saved_view_reproduces_the_identical_view`).
  A chat from before the merge lines imports its `view.json` once, as
  merges.
- **D2. Extra fields.** A message line can carry `key` (an idempotent
  append across crashes). `tree/` also holds the merge lines (D1). The
  gist's fields are all there, unchanged.
- **D3. `eukhe`, not `unii`.** The gist says to rename Unii to the agent's
  name, so the agent's replies are kind `eukhe`, and the prompt's kind list
  says `eukhe`. Lines logged before the rename say `talk`; they read as
  `eukhe`. Old tree lines keep their `talk:` text, since nodes are never
  rebuilt.
- **D4. Static layers.** eukhe's own static tool notes sit between the
  memory prompt and the user's instructions. They do not change, so the
  cache prefix holds. The working directory is part of a session's set-up
  and does not change in a chat's sessions.
- **D5. Retry while a turn waits.** While a turn waits for the view (rule
  47), a failed node is also tried every 10 seconds (`RETRY`). Without this,
  a turn waits for a message that does not come. After 3 failures the wait
  ends with the compactor's error.
- **D6. The model.** The gist names UniiChat's model (Claude Haiku). eukhe
  uses the model in the user's settings (`memory.model`, else the auxiliary
  model).
- **D7. The compaction view at start.** The compaction view is not logged.
  At start it is the view merged down to 16 KB once, as the gist starts it.
  This changes only which prefix the first compactions read from the cache.
- **D8. A crash between a message and its batch line.** While the view
  shrinks, every message writes a batch line, so a restart sees a missing
  line and runs that batch. When the view is not shrinking and a message
  passes 128 KB, the batch line can be lost in a crash. Then the batch runs
  at the next message instead. A restart never runs a batch on its own,
  because the live chat also waits for the next message.
