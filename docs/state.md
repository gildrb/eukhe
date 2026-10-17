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
