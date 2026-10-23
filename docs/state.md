# Harness laws: session state

Shared rules (what a law secures, adversary, H1 to H6): [harness.md](harness.md).

### S1. The session tree

One tree holds a session's state. Node: id, parent, value. Node id > parent id. Root (id `0`) parents the top nodes; the root is not a node.

1. A record changes the tree. `Do` holds one checked change: `Put` sets a node; `Del` removes a node and its subtree. Rejected: `Put` whose parent is not root or a node; `Del` of the root. A rejected record changes nothing.
2. `Rewind` holds exact changes back to an earlier tree. Rejected if the result is not a sound tree.
3. The journal keeps every record in order. Replay of the journal = live tree; replay of a prefix = snapshot. Cursor = number of records.
4. A rewind plan compares live tree and snapshot: stops each node that goes, starts each node that comes back, restores each node that changes.

The state tree is the session tree made by the storage's commits. Disk format unchanged: the tree comes from the commits in `main.jsonl`.

1. Each stored record is a node: conversation, entry, task, submission, document. Conversation: under the conversation of its owning task, else of its fork source, else root. Entry, task, submission: under their conversation. Session document: root. Conversation document: its conversation. Task document: its task's conversation.
2. So each parent is root or a conversation; no commit deletes a conversation. History drops early states of a terminal task, yet each node finds its parent: a build from history first learns each task's conversation.
3. Each change of a commit is one `Do`: new or changed record `Put`; retired document `Del`; copied document `Put`. Changes come unordered: a `Put` waits for its parent.
4. A change whose parent or node is missing is a typed error (`StateError`): tree unchanged, session logs it. Nothing dropped silently.
5. Value: conversation, task, submission = record as JSON. Entry = kind, conversation, head, task. Document = kind, key, scope, creating commit, last changing commit.
6. Ids go in first-seen order. A commit at or before the tree's last commit counts once.
7. On open, storage keeps its replayed history; a background task builds the tree from it, then records each Harness commit. The commit listener only queues, so no commit waits for the tree. Open and attach do not wait for the build; a read does. A panic in build or record stops the tree: it ends its commit subscription; reads get an error.
8. Ids and cursor hold for one worker. A rebuild can see records in another order; after a worker restart a client reads a new snapshot.

Wire: one-shot read, opt-in subscription.

1. `get_state_tree`: snapshot (with cursor), or records after cursor `since`. `get_state_rewind_plan`: effects of a rewind to a cursor.
2. `subscribe_state_tree`: same reply. The supervisor adds the connection to the session's state tree subscribers before the worker reads the tree; then each commit that adds records sends a `state_tree_update` frame (`from`, `cursor`, records). Frames cover every record after the reply's cursor.
3. Frames can repeat reply records. Client skips a frame with `cursor` <= its own; else applies records from its own cursor. `from` > client cursor = loss: subscribe again.
4. `unsubscribe_state_tree` or a closed connection ends it. Non-subscribers never get the frame. The frame is not a session event: no event sequence, so other clients' replay cursors are unchanged. A direct session client of the worker never gets it.

Model: `bend/tree.bend`. Laws: `laws/tree.bend` (S1). Proofs: `proof/tree/`. All laws universal: any record (any put, valid or not, any delete, any rewind ops).

| Law | Says |
| --- | --- |
| `tree_apply_sound` | Sound tree stays sound: ids ordered, no orphan, no cycle (S1.1, S1.2). |
| `tree_replay_sound` | Any journal → sound tree (S1.3). |
| `tree_snapshot` | Prefix snapshot + later records = whole-journal tree (= live tree for a client) (S1.3). |
| `tree_rewind_reaches` | Rewind by diff live→target = target exactly (S1.2, S1.4). |
| `tree_rewind_still` | Rewind to live = no changes (S1.4). |
| `tree_rewind_minimal` | Rewind touches only nodes differing between live and target (S1.4). |
| `tree_delete_removes` | Delete removes its node (S1.1). |
| `tree_delete_only_below` | Delete removes only its subtree (S1.1). |
| `tree_delete_within` | Delete changes no kept node (S1.1). |
| `tree_put_sets` | Put under root or a node sets it (S1.1). |
| `tree_put_keeps_others` | Put changes no other node (S1.1). |
| `tree_core_tree` | Compiled core's tree after any journal (key map, splits halve the key range) = the journal's tree (S1.3). |
| `tree_core_answer` | After any journal, the core answers each record as the model decides: taken or kept; a delete cuts exactly the nodes it removes (S1.1, S1.2). |
| `tree_core_note` | A record steps the core to the core of the journal with that record appended, so core laws hold for the live core (S1.3). |
| `tree_core_plan` | Core's rewind plan to the tree after the first n records = what the live→that-tree diff does to each node's work (S1.4). |
| `tree_core_snap` | Core's snapshot after the first n records = their replay (S1.3). |
| `tree_core_plan_keeps`, `tree_core_snap_keeps` | Rewind plan and snapshot leave the core unchanged. |
| `tree_ffi_ask_round_trip` | Every record and question the Rust journal writes reads back in the core's entry (`bend/ffi_tree.bend`). |
| `tree_ffi_step` | An entry step answers the core's answer, keeps the core's next state. |
| `tree_ffi_open` | The entry opens the empty core with the halves the journal sends. |
| `tree_ffi_malformed`, `tree_ffi_trailing`, `tree_ffi_refused`, `tree_ffi_open_malformed`, `tree_ffi_open_trailing` | Any other input answers the wire's error form, never a default; a step keeps the core. |
| `tree_ffi_example` | Tags and field order Rust writes and reads. |

Code: `eukhe-durable/src/tree/mod.rs` `SessionTree`, `TreeRecord`, `TreeOp`; `tree/journal.rs` `Journal` (`push`, `snapshot_at`, `rewind_plan`: shell over a stepper of the compiled Bend core, `bend/ffi_tree.bend` through `eukhe-bend`; equal values share one value index); `tree/state.rs` `StateTree` (`record`, `from_history`, `record_writes`, `records_since`, `snapshot_at`, `rewind_plan`); `storage/jsonl/storage.rs` `CommitHistory`, `JsonlStorage::take_history`; `eukhe-core/src/durable/state_tree.rs` `LiveStateTree`; `eukhe-daemon/src/worker/state_tree.rs` (`get_state_tree`, `subscribe_state_tree`, `get_state_rewind_plan`, `state_tree_update`); `supervisor/clients.rs` (subscription, `state_tree_subscribers`); `supervisor/supervision.rs` (frame routing); `peer.rs` `ConnectionRole::streams`; `eukhe-cli/src/daemon_command.rs` `run_state` (`eukhe state`, `--follow`, `rewind-plan`).

Tie: the journal decides every record, rewind plan and snapshot by one step of its stepper (the compiled model), whose state is the live tree and the journal; a record costs its change and a lookup (a delete walks only its node and nodes with a parent of its key or more), not the tree.

Tests (glue around the core): `tree::journal::tests::the_live_tree_follows_the_core`, `tree::state::tests::commits_build_the_tree_with_parents_first`, `storage_writes_build_the_same_journal_as_publications`, `a_rewind_plan_stops_starts_and_restores`, `a_history_gives_every_node_its_conversation`, `an_unknown_parent_or_node_is_an_error`; `jsonl_storage::keeps_the_replayed_and_later_commits_until_the_history_is_taken`; `durable::open::tests::the_state_tree_follows_the_history_and_the_live_commits`; daemon `get_state_tree_answers_the_sessions_tree`, `subscribe_state_tree_streams_records_to_its_connection_only`; `peer::tests::peer_session_attach_gates_event_stream`.

Not modelled: commit→record map (S1, second list); tested.

### D2. Storage and cron

Storage = a directory with one commit log, `main.jsonl`; opened with fsync on in each worker.

1. Commit: append one line to `main.jsonl`, flush the file. First commit after open also flushes the storage directory (entry of `main.jsonl`); open flushes the parent directory (entry of the storage directory). Only then is the commit acknowledged.
2. A crash can come at any step: keeps flushed bytes and any prefix of unflushed bytes; can lose unflushed directory entries.
3. Open reads complete lines only; cuts a torn tail (bytes after the last newline), never read as a commit.

A new storage (legacy import, fork) builds in a staging directory beside its place: `.<name>.import-<uuid>` or `.<name>.fork-<uuid>`.

1. The builder creates `<staging>.lock` first and holds an exclusive lock until the build ends.
2. Publish renames staging into place only if no entry has the name (`RENAME_NOREPLACE`). An existing entry, even an empty directory, stays; the build fails with "exists".
3. Sweep: at boot and every 5 minutes, every depth of the sessions directory and `session-artifacts`; never enters a storage, symlink or leftover. Removes a staging directory, delete tombstone, or lock file without its directory, when no live process holds its lock and it is untouched for a day.

Listing shows storage directories (not hidden, with `main.jsonl` and a readable cwd) and legacy files `<stem>.jsonl`. A legacy file lists under its stem (the storage name every open imports it into), only while no directory has that name. So a session lists once, before and after import.

Models: `bend/log.bend`, `bend/staging.bend`. Laws: `laws/log.bend`, `laws/staging.bend`. Proofs: `proof/log/` and `proof/staging/`.

| Law | Says |
| --- | --- |
| `log_reads_lines` | Open reads exactly the complete lines, in order; never a torn tail. |
| `log_ack_durable` | Post-crash log = old log + all acked commits + maybe more. |
| `log_only_commits` | Post-crash log = old log + prefix of tried commits. |
| `publish_never_overwrites` | Taken name: publish fails, no change. |
| `publish_moves` | Free name: publish moves the storage. |
| `sweep_never_live` | Never removes a live-locked entry. |
| `sweep_never_young` | Never removes an entry touched within the day. |
| `sweep_stays_out` | Never removes an unreached entry. |
| `sweep_reaches_every_depth` | Removes every free, stale, reached leftover. |
| `list_one_location` | No name listed as both storage and legacy file. |
| `list_import_lists_storage` | After import, the stem lists as storage. |
| `list_import_keeps_others` | Import changes no other listing. |

Code: `eukhe-durable/src/storage/jsonl/storage.rs` (`JsonlStorage::open`, commit path, `read_lines`); `eukhe-core/src/durable/staging.rs` (`lock_staging`, `publish`, `sweep_stale_staging_dirs`); `platform/fs.rs` `rename_no_replace`; `durable/discovery.rs` `list_sessions`; `eukhe-daemon/src/session_archive.rs` (sweep loop).

Bridges: `storage::jsonl::bridge::the_commit_log_runs_as_its_model` (real `JsonlStorage`, power loss after any step, every crash point of a three-commit epoch, 120 random histories); `durable::staging::bridge::staging_sweep_and_listing_run_as_their_model` (every target kind, 60 sweep trees, 30 sessions directories with imports).

Tests: `durable::staging::tests::publish_never_replaces_an_entry_at_the_target`, `a_held_staging_dir_is_never_swept`, `sweeps_leftovers_at_every_depth_it_owns`.

#### The cron store

All processes of an agent directory share the cron jobs file (`cron-jobs.json`, or a session's `scheduled-jobs.json`). `AgentCronJobStore` (crates/eukhe-core/src/cron/store/):

1. A claim belongs to its owner. Each dispatch record names its claiming process (pid and start identity, `ProcessIdentity`). Recovery clears a claim only if it is this process's and its run is no longer live (pass unwound), or its owner is dead. Another process's live claim stays.
2. A one-shot job completes only by its run's finish step, or by recovery of a claim whose run ended. A claim never completes it.
3. Nothing dropped. Unparseable job or claim records, and unknown top-level keys, stay as they are. A file that exists but cannot be read or parsed is never overwritten: the next update moves it to `<name>.corrupt-<ms>-<id>` and starts empty. Only a missing file reads as empty.
4. A failing job stops. Each failure delays the next run by 2, 4, 8, 16, 32, then 60 minutes (never before schedule); the pause never shrinks in a streak. After `FAILURE_STOP_AFTER` (8) failures in a row: paused with its error; cron list shows `paused`, `failures=8`, the error. Only a user action restarts it (resume sets the count to 0). A good run sets the count to 0. Failure 8 comes about three hours after failure 1; the last two pauses are one hour each: a cause that lasts this long is not a short outage.

Model: `bend/cron.bend`. Laws: `laws/cron.bend` (`cron_fires_once`, `cron_once_finished_after_end`, `cron_never_drops`, `cron_claim_owned`, `cron_backoff_bounded`). Proofs: `proof/cron/`.

Bridge: `cron::store::bridge::the_rust_cron_store_equals_the_bend_model`: 3 simulated processes (own store, owner identity, liveness seam, fake clock), one file, byte-equal to `bend/bridge_cron.bend`. Not modelled: cron expressions (model: one-shot, interval); freshness merge of whole-list writes (bridge steps one at a time).

Tests (`cron::store::jobs::tests`): `a_pass_of_another_process_keeps_a_live_claim`, `a_one_shot_is_not_completed_while_it_runs`, `an_unread_job_survives_a_create`, `a_corrupt_file_is_moved_aside`, `a_failing_job_stops_after_the_cap`.
