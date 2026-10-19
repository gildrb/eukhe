# Harness laws: session state

The shared rules (what a law secures, the adversary, H1 to H6) are in [harness.md](harness.md).

### S1. The session tree

One tree holds the state of a session. Each node has an id, a parent and a
value. The id of a node is more than the id of its parent. The root (id
`0`) is the parent of the top nodes. The root is not a node.

1. A record changes the tree. A `Do` record holds one checked change: a
   `Put` sets a node, and a `Del` removes a node and every node below it.
   The tree rejects a `Put` whose parent is not the root or a node, and a
   `Del` of the root. A rejected record does not change the tree.
2. A `Rewind` record holds exact changes back to an earlier tree. The tree
   rejects a rewind whose result is not a sound tree.
3. The journal keeps every record in order. A replay of the journal makes
   the live tree. A replay of a prefix is a snapshot. The cursor is the
   number of records.
4. A rewind plan compares the live tree with a snapshot. It stops each
   node that goes, starts each node that comes back, and restores each
   node that changes.

The state tree of a session is a session tree that the commits of its
storage make. The disk format does not change: the tree comes from the
same commits that `main.jsonl` holds.

1. Each stored record is a node: a conversation, an entry, a task, a
   submission, or a document. A conversation hangs under the
   conversation of the task that owns it, else under the conversation
   that it forks from, else under the root. An entry, a task, and a
   submission hang under their conversation. A session document hangs
   under the root. A conversation document hangs under its conversation.
   A task document hangs under the conversation of its task.
2. So the parent of each node is the root or a conversation, and no
   commit deletes a conversation. The stored history does not keep the
   early states of a terminal task, but each node still finds its
   parent. A build from the history first learns the conversation of
   each task.
3. Each change of a commit is one `Do` record. A new or changed record is
   a `Put`. A retired document is a `Del`. A copied document is a `Put`.
   The changes of a commit come in no order: a `Put` waits until its
   parent is in the tree.
4. A change whose parent or node is not in the tree is a typed error
   (`StateError`). The tree does not change, and the session logs the
   error. Nothing is dropped in silence.
5. The value of a conversation, a task, and a submission node is its
   record as JSON. An entry node keeps its kind, conversation, head, and
   task. A document node keeps its kind, key, scope, the commit that
   made it, and the commit that last changed it.
6. Ids go to records in the order that the tree first sees them. A
   commit at or before the last commit of the tree counts once.
7. On open, the storage keeps its replayed history. A background task
   builds the tree from it. Then the task records each commit of the
   Harness. The commit listener only puts the commit in a queue, so no
   commit waits for the tree. Open and attach do not wait for the build.
   A read waits until the build ends. If the build or a record panics,
   the tree stops: it ends its commit subscription, and a read gets an
   error.
8. The ids and the cursor hold for one worker. A tree built again from
   the stored history can see the records in another order. After a
   worker restart, a client reads a new snapshot.

The wire has a one-shot read and an opt-in subscription.

1. `get_state_tree` gives the snapshot (with its cursor), or the records
   after the cursor `since`. `get_state_rewind_plan` gives the effects of
   a rewind to a cursor.
2. `subscribe_state_tree` gives the same reply. The supervisor adds the
   connection to the session's state tree subscribers before the worker
   reads the tree. Then the connection gets a `state_tree_update` frame
   (`from`, `cursor`, and the records) after each commit that adds
   records. So the frames cover every record after the reply's cursor.
3. A frame can repeat records that the reply had. A client skips a frame
   whose `cursor` is not more than its own cursor. For the other frames,
   it applies the records from its own cursor. A frame whose `from` is
   more than the client's cursor shows a loss: the client subscribes
   again.
4. `unsubscribe_state_tree` or a closed connection ends the subscription.
   A connection that does not subscribe never gets the frame. The frame is
   not a session event: it takes no event sequence, so the replay cursors
   of other clients do not change. A direct session client of the worker
   never gets the frame.

Model: `bend/tree.bend`. Laws: `LAWS.bend` section (S1). Proofs:
`bend/proof_tree.bend`. Every law is universal: every record is free (any
put, valid or not, any delete, any rewind ops).

| Law | Says |
| --- | --- |
| `tree_apply_sound` | A record keeps a sound tree sound: the ids are in order, and every node hangs under the root or a node (no orphan, no cycle) (S1.1, S1.2). |
| `tree_replay_sound` | Every journal makes a sound tree (S1.3). |
| `tree_snapshot` | A snapshot after a prefix of the journal, with the records after it, makes the tree of the whole journal. A client that holds a snapshot and gets the records after it holds the live tree (S1.3). |
| `tree_rewind_reaches` | A rewind with the diff from the live tree to a target makes the target exactly (S1.2, S1.4). |
| `tree_rewind_still` | A rewind to the live tree has no changes (S1.4). |
| `tree_rewind_minimal` | Each change of a rewind is on a node that differs between the live tree and the target: a rewind starts, stops, or restores only what changed (S1.4). |
| `tree_delete_removes` | A delete removes its node (S1.1). |
| `tree_delete_only_below` | A delete removes a node only when it is the deleted node or its parent goes: it removes the subtree, nothing else (S1.1). |
| `tree_delete_within` | A delete changes no node that it keeps (S1.1). |
| `tree_put_sets` | A put under the root or a node sets its node (S1.1). |
| `tree_put_keeps_others` | A put changes no other node (S1.1). |

Code: `eukhe-durable/src/tree/mod.rs` `SessionTree::apply`, `TreeRecord`,
`TreeOp`; `tree/journal.rs` `Journal` (`push`, `replay`, `snapshot_at`);
`tree/diff.rs` `diff`, `rewind_to`, `rewind_effects`; `tree/state.rs`
`StateTree` (`record`, `from_history`, `record_writes`, `records_since`, `snapshot_at`,
`rewind_plan`); `storage/jsonl/storage.rs` `CommitHistory`,
`JsonlStorage::take_history`; `eukhe-core/src/durable/state_tree.rs`
`LiveStateTree`; `eukhe-daemon/src/worker/state_tree.rs` (the
`get_state_tree`, `subscribe_state_tree`, and `get_state_rewind_plan`
requests, and the `state_tree_update` frame);
`supervisor/clients.rs` (the subscription, `state_tree_subscribers`);
`supervisor/supervision.rs` (the frame routing); `peer.rs`
`ConnectionRole::streams`; `eukhe-cli/src/daemon_command.rs` `run_state`
(`eukhe state`, `eukhe state --follow`, `eukhe state rewind-plan`).

Tie: the bridge test `tree::bridge::the_rust_tree_equals_the_bend_model`
runs `Journal` and `bend/bridge_tree.bend` on 300 generated scenarios
(checked puts and deletes, saves, rewinds to a save, raw rewinds, and
replays of the journal) and compares the transcripts byte for byte. The
scenarios reach every rule of the model. Regression tests:
`tree::state::tests::commits_build_the_tree_with_parents_first`,
`storage_writes_build_the_same_journal_as_publications`,
`a_rewind_plan_stops_starts_and_restores`,
`a_history_gives_every_node_its_conversation`,
`an_unknown_parent_or_node_is_an_error`;
`jsonl_storage::keeps_the_replayed_and_later_commits_until_the_history_is_taken`;
`durable::open::tests::the_state_tree_follows_the_history_and_the_live_commits`;
the daemon tests `get_state_tree_answers_the_sessions_tree` and
`subscribe_state_tree_streams_records_to_its_connection_only`;
`peer::tests::peer_session_attach_gates_event_stream`. Not modelled:
the map from commits to records (S1, second list). Its tests tie it.

### D2. Storage and cron

A session's storage is a directory with one commit log, `main.jsonl`.
A storage opens with fsync on in each worker.

1. A commit appends one line to `main.jsonl` and flushes the file. The
   first commit after an open also flushes the storage directory (the
   entry of `main.jsonl`). An open also flushes the parent directory
   (the entry of the storage directory). Only then is a commit
   acknowledged.
2. A crash can come at any step. It keeps the flushed bytes and any
   first part of the bytes that are not flushed. It can also lose the
   directory entries that are not flushed.
3. An open reads only complete lines. It cuts a torn tail (the bytes
   after the last newline) and never reads it as a commit.

A new storage (an import of a legacy file, a fork) is built in a staging
directory beside its place, `.<name>.import-<uuid>` or
`.<name>.fork-<uuid>`.

1. The builder creates the lock file `<staging>.lock` first and holds an
   exclusive lock on it until the build ends.
2. The publish renames the staging directory to its place only when no
   entry has that name (`RENAME_NOREPLACE`). An entry at the target, even
   an empty directory, stays as it was, and the build fails with "exists".
3. The sweep runs at boot and every 5 minutes. It walks every depth of
   the sessions directory and of `session-artifacts`. It does not go into
   a storage, a symlink or a leftover. It removes a staging directory, a
   delete tombstone, or a lock file without its directory, when no live
   process holds its lock and nothing touched it for a day.

The listing of a sessions directory shows a storage directory (not
hidden, with `main.jsonl` and a cwd that reads) and a legacy file
`<stem>.jsonl`. A legacy file is listed under its stem, the name of the
storage that every open imports it into, and only while no directory
has that name. So a session is listed once, before and after its
import.

Models: `bend/log.bend`, `bend/staging.bend`. Laws: `laws/storage.bend`.
Proofs: `bend/proof_log.bend`, `bend/proof_staging.bend`.

| Law | Says |
| --- | --- |
| `log_reads_lines` | An open reads exactly the complete lines, in order; a torn tail is never read. |
| `log_ack_durable` | After any crash, the log is the old log, then every acknowledged commit, then maybe more. |
| `log_only_commits` | After any crash, the log is the old log, then a prefix of the commits tried. |
| `publish_never_overwrites` | A publish to a taken name fails and changes nothing. |
| `publish_moves` | A publish to a free name moves the storage. |
| `sweep_never_live` | A sweep never removes an entry whose lock a live process holds. |
| `sweep_never_young` | A sweep never removes an entry touched within the day. |
| `sweep_stays_out` | A sweep never removes an entry it does not reach. |
| `sweep_reaches_every_depth` | A sweep removes every free, stale leftover it reaches. |
| `list_one_location` | No name is listed both as a storage and as a legacy file. |
| `list_import_lists_storage` | After an import, the stem is listed as a storage. |
| `list_import_keeps_others` | An import changes the listing of no other name. |

Code: `eukhe-durable/src/storage/jsonl/storage.rs` (`JsonlStorage::open`,
the commit path, `read_lines`); `eukhe-core/src/durable/staging.rs`
(`lock_staging`, `publish`, `sweep_stale_staging_dirs`);
`platform/fs.rs` `rename_no_replace`; `durable/discovery.rs`
(`list_sessions`); `eukhe-daemon/src/session_archive.rs` (the sweep
loop).

Tie: the bridge tests
`storage::jsonl::bridge::the_commit_log_runs_as_its_model` (the real
`JsonlStorage` over a file system that loses power after any step, at
every crash point of a three-commit epoch and on 120 random histories)
and `durable::staging::bridge::staging_sweep_and_listing_run_as_their_model`
(publishes to every kind of target, 60 generated sweep trees, 30
generated sessions directories with imports). Regression tests:
`durable::staging::tests::publish_never_replaces_an_entry_at_the_target`,
`a_held_staging_dir_is_never_swept`,
`sweeps_leftovers_at_every_depth_it_owns`.

#### The cron store

The cron jobs file (`cron-jobs.json`, or a session's
`scheduled-jobs.json`) is shared by all processes of an agent directory.
`AgentCronJobStore` (crates/eukhe-core/src/cron/store/) keeps these rules:

1. A claim belongs to its owner. Each dispatch record names the process
   that claimed it (pid and start identity, `ProcessIdentity`). A
   recovery clears a claim only when it is the claim of this process and
   its run is no longer live (the pass unwound), or when its owner is
   dead. The live claim of another process stays.
2. A one-shot job is completed only by the finish step of its run, or
   by the recovery of a claim whose run ended. A claim never completes it.
3. Nothing is dropped. A job record or a claim record that does not parse
   stays in the file as it is, and so do top-level keys the store does
   not know. A file that exists but cannot be read or parsed is never
   written over: the next update moves it aside as
   `<name>.corrupt-<ms>-<id>` and starts from an empty file. Only a
   missing file reads as empty.
4. A failing job stops. Each failed run pushes the next run out by
   2, 4, 8, 16, 32 minutes, then 60 minutes (never earlier than the
   schedule). The pause never gets shorter in a streak. After
   `FAILURE_STOP_AFTER` (8) failures in a row the job is paused with its
   error, and the cron list shows `paused`, `failures=8` and the error.
   Only a user action starts it again (a resume sets the count to 0). A
   good run sets the count to 0. The eighth failure comes about three
   hours after the first, and the last two pauses are one hour each: a
   cause that lasts this long is not a short outage.

Laws: `laws/cron.bend` (`cron_fires_once`, `cron_once_finished_after_end`,
`cron_never_drops`, `cron_claim_owned`, `cron_backoff_bounded`) about the
model `bend/cron.bend`, proved in `bend/proof_cron.bend` and
`bend/proof_cron_step.bend`. Tie: the bridge test
`cron::store::bridge::the_rust_cron_store_equals_the_bend_model` runs
three simulated processes (each with its own store and owner identity,
a liveness seam and a fake clock) on one file, and compares its
transcript with `bend/bridge_cron.bend` byte for byte. Not modelled: cron
expressions (the model has one-shot and interval schedules), and the
freshness merge of whole-list writes (the bridge runs one step at a time).
Regression tests in `cron::store::jobs::tests`:
`a_pass_of_another_process_keeps_a_live_claim`,
`a_one_shot_is_not_completed_while_it_runs`,
`an_unread_job_survives_a_create`, `a_corrupt_file_is_moved_aside`,
`a_failing_job_stops_after_the_cap`.
