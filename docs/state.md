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

### S2. The task lifecycle (`task_life`)

A durable task (pi-durable spec §5.1-§5.5) is `pending`, `running` or `waiting` (live, with a checkpoint), `completing` (outcome decided, held while ordinary owned work below is live; runs no code) or `terminal`.

1. A terminal task never changes.
2. Reservation: a pending, running or waiting task becomes running at the same checkpoint. A completing task is not reserved.
3. Only a running task commits (running, waiting, an outcome) or goes back to pending (handover to a replacement definition), at its own checkpoint.
4. An outcome (a commit, or a fault or orphan the scheduler writes for a live task that is not completing) is completing while owned work is live, else terminal. Finalization: completing becomes terminal with the same outcome when no owned work is live.
5. Resume (a new Harness): running becomes pending at its checkpoint; a failFast wait is checked again; nothing else changes.
6. Join: a waiting task runs when no awaited task is live. allSettled marks nothing. failFast, after an awaited task holds or ended with an outcome other than completed, marks each live awaited task that did not fail.
7. Abort marks: none < restart < request. A new mark keeps the stronger.
8. Cascade: below a live owner with intent (a mark, or a held outcome other than completed), each live foreground task that the owner's walk reaches takes the owner's reason: restart from an owner with the restart mark that did not fail, else request. Nothing else changes.
9. A submission status moves only forward: queued, placed, then done or unanswered.

Model: `bend/task_life.bend`, entry `bend/ffi_task_life.bend` (id 432). Spec (independent restatement): `spec/durable/task_life.bend`; the entry's spellers, bounds and reader: `spec/durable/task_life_wire.bend`. Laws: `laws/task_life.bend`. Proofs: `proof/task_life/`. All laws universal: any state, transition, handle, policy, mark, list.

| Law | Says |
| --- | --- |
| `task_life_step_refines_spec` | Each transition of each state = the spec's (by transition first), refusal reason included (S2.1-S2.4). |
| `task_life_terminal_absorbs` | Terminal: every transition refused as ended; resume keeps it (S2.1). |
| `task_life_outcome_once` | From completing with outcome o: refused, still completing with o, or terminal with o (S2.4). |
| `task_life_forward_only` | No transition and no resume lowers the measure pending < running, waiting < completing < terminal, except a running task back to pending at its own checkpoint (S2.2-S2.5). |
| `task_life_resume_keeps_checkpoint` | Resume keeps each checkpoint and outcome; no task stays running (S2.5). |
| `task_life_resume_exact` | Resume = the spec's, failFast check included (S2.5). |
| `task_life_join_fail_fast`, `task_life_join_all_settled` | Each policy's join = the spec's: ready iff no awaited task live; marks (S2.6). |
| `task_life_mark_merge` | Merge = the stronger mark (S2.7). |
| `task_life_abort_reaches_owned` | Cascade = the spec's: exactly the live foreground reached tasks below an owner with intent, with its reason (S2.8). |
| `task_life_submission_forward` | Each change of the submission rule (`bend/submission.bend`) moves the status strictly forward or leaves it (S2.9). |
| `task_life_example` | Anchor: the scheduler's sequence. |
| `task_life_entry_answers`, `task_life_entry_reads`, `task_life_entry_malformed_exact`, `task_life_entry_example` | The entry answers each request Rust writes with the rules' decision; any other input gets exactly `E task_life: malformed request`. |

Code: `eukhe-bend` `rules/task_life.rs` (`step`, `resume`, `join`, `merge`, `cascade`); `eukhe-durable` `harness/scheduler/life.rs` (the records' adapter: handle 0 = the record's checkpoint or outcome, 1 = the one the transition brings; a waiting state's awaited tasks travel with its checkpoint).

| Decision site | Rule |
| --- | --- |
| `scheduler/reservation.rs` reservation pass (`life::reserve`) | S2.2 |
| `scheduler/reservation.rs` abandoned tasks at open (`life::marked`, restart) | S2.7 |
| `scheduler/execution.rs` `decide` handover (`life::requeue`) | S2.3 |
| `scheduler/execution.rs` `commit_state` (`life::commit`) | S2.3, S2.4 |
| `scheduler/cascade.rs` `terminate` (`life::settle`) | S2.4 |
| `scheduler/cascade.rs` `finalize` (`life::finalize`) | S2.4 |
| `scheduler/mirror.rs` `open` (`life::resume`) | S2.5 |
| `scheduler/cascade.rs` `reconcile` failFast check (`life::join`, `members`) | S2.6 |
| `scheduler/cascade.rs` `abort`, `abort_conversation` (`life::marked`, request); `Marks` (`life::merge`) | S2.7 |
| `scheduler/cascade.rs` `reconcile` cascade (`life::cascade`) | S2.8 |

Not routed (Rust): the ownership walks that find owned work and the reach of a cascade (`ownership.rs` `walk_down`, `has_owned_live`, `below_cancelled`; the rules decide from their rows); the index predicates `cancellation_intent`, `failed_outcome` (`ownership.rs`); the invocation precedence rules of a run step (`execution.rs` `decide`: abort mark, owner cancellation, uncaught error, no durable progress); wait validation (`execution.rs` `validate_wait`: wait cycles, failFast only on owned tasks); readiness of a task in the reservation pass (`reservation.rs`: owned work of an abort-marked task, live awaited tasks; S2.6 states the same rule); orphaning a blocked task (`cascade.rs` `abort`, `reservation.rs` abort mode) and the `KeepRestart` guard; when a failFast check is scheduled (`mirror.rs` `observe`); the checkpoint rewrite of a migration (`reservation.rs` `resolve`, same state); the Session's guard on any record replacement (`session/transaction.rs`, "already terminal") and the runtime commit gate (`scheduler/runtime.rs`, running only, no abort mark in a run).

Tests: `eukhe_bend::rules::task_life::tests` (the codec through the core); `harness::scheduler::life::tests` (one per routed decision).

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

Models: `bend/log.bend`, `bend/staging.bend`. Laws: `laws/log.bend`, `laws/staging.bend`. Proofs: `proof/log/` and `proof/staging/`. The commit log's rules run as compiled Bend (`bend/log.bend` section "The rules", entry `bend/ffi_log.bend`, id 33): what an open does with a file (`tail`, from its length and last newline), and the plan of steps at open and per commit (`Store.open`, `Store.commit`, a stepper); `JsonlStorage` reads the facts and does the steps (`storage/jsonl/plan.rs`).

| Law | Says |
| --- | --- |
| `log_reads_lines` | Open reads exactly the complete lines, in order; never a torn tail. |
| `log_ack_durable` | Post-crash log = old log + all acked commits + maybe more. |
| `log_only_commits` | Post-crash log = old log + prefix of tried commits. |
| `log_open_cuts_the_torn_tail`, `log_open_keeps_the_complete_lines`, `log_open_refuses_odd_facts` | An open keeps a file whose bytes are all in complete lines, cuts any other to exactly the bytes of the lines open reads (`Lg.recover`); refuses facts no file has. |
| `log_plan_runs_the_model`, `log_plan_ack_durable`, `log_plan_only_commits` | The plan of an fsync open and its commits, cut after any step, is the model's epoch (`Lg.run`): acked commits survive, only a prefix of commits is read. |
| `log_commit_plan`, `log_open_plan` | Every commit's plan for every storage and sidecar list: records, (fsync) their flushes and a directory flush while an entry is new, marker, (fsync) its flush and a directory flush while main.jsonl's entry is new, ack. |
| `log_ffi_*`, `log_stepper_*` | The entry answers the requests Rust writes with the rule's decisions, the error form to anything else; a refused step keeps the state. |
| `publish_never_overwrites` | Taken name: publish fails, no change. |
| `publish_moves` | Free name: publish moves the storage. |
| `sweep_never_live` | Never removes a live-locked entry. |
| `sweep_never_young` | Never removes an entry touched within the day. |
| `sweep_stays_out` | Never removes an unreached entry. |
| `sweep_reaches_every_depth` | Removes every free, stale, reached leftover. |
| `list_one_location` | No name listed as both storage and legacy file. |
| `list_import_lists_storage` | After import, the stem lists as storage. |
| `list_import_keeps_others` | Import changes no other listing. |
| `publish_settles`, `publish_settle_refines` | The real publish verdict: taken exactly when the rename without replacement met an entry; the model's publish. |
| `meet_exact`, `meet_minted_*`, `sweep_stays_out_real` | What the sweep does with each entry of a listing (enter, keep, judge a leftover or an orphan lock file), by name and type. |
| `judge_exact`, `judge_refines`, `sweep_never_live_real`, `sweep_never_young_real`, `sweep_takes_stale_free_real` | The plan for a judged entry from its lock probe and times (a day, to the nanosecond); the model's `removes`. |
| `scan_*` (`laws/listing.bend`) | Which entry of the sessions directory is a session, under which id; one location per id; imports. |
| `rows_*` | The listing: every candidate with a cwd and a file, once, as its entry, newest first, then by id, then by place; unread facts of skipped entries ignored. |
| `staging_entry_*` | The entry answers the requests Rust writes with the rule's decisions, the error form to anything else. |

Code: `eukhe-durable/src/storage/jsonl/storage.rs` (`JsonlStorage::open`, `run_plan`, commit path, `read_lines`), `storage/jsonl/plan.rs` (the calls of the compiled core); `eukhe-core/src/durable/staging.rs` (`lock_staging`, `publish`, `sweep_stale_staging_dirs`: the facts and the steps), `durable/staging/rule.rs` (the calls of the compiled core, entry `bend/ffi_staging.bend`); `platform/fs.rs` `rename_no_replace`; `durable/discovery.rs` `list_sessions`; `eukhe-daemon/src/session_archive.rs` (sweep loop).

Crash test of the commit log's IO shell: `storage::jsonl::crash::a_crash_at_any_step_keeps_the_acknowledged_commits_and_only_commits` (real `JsonlStorage` over a file system that loses power after any step, every crash point of a three-commit epoch, 120 random histories: the log after is the log before, the acked commits, then only a prefix of the commits).

Tests: `durable::staging::tests::publish_never_replaces_an_entry_at_the_target`, `a_held_staging_dir_is_never_swept`, `sweeps_leftovers_at_every_depth_it_owns`.

#### The cron store

All processes of an agent directory share the cron jobs file (`cron-jobs.json`, or a session's `scheduled-jobs.json`). `AgentCronJobStore` (crates/eukhe-core/src/cron/store/):

1. A claim belongs to its owner. Each dispatch record names its claiming process (pid and start identity, `ProcessIdentity`). Recovery clears a claim only if it is this process's and its run is no longer live (pass unwound), or its owner is dead. Another process's live claim stays.
2. A one-shot job completes only by its run's finish step, or by recovery of a claim whose run ended. A claim never completes it.
3. Nothing dropped. Unparseable job or claim records, and unknown top-level keys, stay as they are. A file that exists but cannot be read or parsed is never overwritten: the next update moves it to `<name>.corrupt-<ms>-<id>` and starts empty. Only a missing file reads as empty.
4. A failing job stops. Each failure delays the next run by 2, 4, 8, 16, 32, then 60 minutes (never before schedule); the pause never shrinks in a streak. After 8 failures in a row: paused with its error; cron list shows `paused`, `failures=8`, the error. Only a user action restarts it (resume sets the count to 0). A good run sets the count to 0. Failure 8 comes about three hours after failure 1; the last two pauses are one hour each: a cause that lasts this long is not a short outage.

Model: `bend/cron.bend` (the file shared by processes, minutes). Laws: `laws/cron.bend` (`cron_fires_once`, `cron_once_finished_after_end`, `cron_never_drops`, `cron_claim_owned`, `cron_backoff_bounded`). Proofs: `proof/cron/`.

The per-job decisions run as the compiled core: entry `bend/ffi_cron.bend` (id 82) over `bend/cron_store.bend` (ms), called by `eukhe-bend` `rules::cron` (`take`, `clear`, `recover`, `finish`, `cancel`, `resume`). The store (`store/facts.rs`) gathers one job's facts (status, schedule, next run, failures in a row, a claim on record or cleared, whose a claim is: `owner.rs` `ClaimOwner::who` from the running set and the liveness probe) and writes back what the core answers; it keeps the file, its lock, the claim records, ids, cron expressions (a rule's next match), write and fsync. Laws (D2.2): `cron_entry_answers`, `cron_entry_malformed_exact`, `cron_entry_example`, `cron_entry_fits_example`, and `cron_take_refines`, `cron_recover_refines`, `cron_finish_refines`, `cron_cancel_refines`, `cron_resume_refines` (on a clock of any unit, a minute being 60000 ms, each decision applied to a model job is the model's step).

Bridge (the interleaving only): `cron::store::bridge::the_rust_cron_store_equals_the_bend_model`: 3 simulated processes (own store, owner identity, liveness seam, fake clock), one file, byte-equal to `bridge/bridge_cron.bend`. It checks the shell around the proven decisions: claim records of several processes, unread records kept, a corrupt file moved aside. Not modelled: cron expressions (model: one-shot, interval); freshness merge of whole-list writes (bridge steps one at a time).

Tests (`cron::store::jobs::tests`, file IO): `an_unread_job_survives_a_create`, `a_corrupt_file_is_moved_aside`; the core is reached: `eukhe_bend::rules::cron::tests::the_cron_decisions_come_from_the_compiled_core`.
