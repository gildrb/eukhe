# record (spec): the complete replayable record

Status: spec only. Nothing below is implemented; no law named in section 4
exists yet. Ids `T1..T12` are provisional.

Every decision and every effect of every agent is written down with who
caused it. The record shows when it was changed. A session can be replayed
from it to the same decisions, with no effect. One query audits a whole tree
of agents. The pillar builds on the commit log, the session tree's journal,
the tool-call gate (intent before effect), the versioned tool calls and the
input origins; it adds what is missing: decisions as entries, causes, a hash
chain with anchors, the replay, and the audit across agents.

## 1. Words

- **record**: per session, one ordered list of entries, append only. It is
  the session's commit log seen as evidence, not a second store.
- **entry kinds**: an **input** is a fact from outside the harness (a user's
  words, a model's reply, a tool's output, a client's answer, a clock
  reading, a file's content digest, a setting's value). A **decision** is one
  call of a rule of the compiled core: which rule, which inputs, the answer.
  An **effect** is something done to the world: its intent, then its outcome.
- **author**: the principal an entry is attributed to: a user (through which
  client), an agent, the harness itself (a timer, a restart).
- **cause**: the earlier entries an entry was made from. An **origin** is an
  entry with no cause: only a user's input, a schedule firing, or the
  harness's own start; nothing else may be one.
- **head**: the pair (length, digest) that stands for a whole record.
  **anchor**: a head of one record stored where its writer cannot rewrite it
  (the parent's record, the daemon's ledger). **anchor point**: when a head
  is anchored: a spawn, a report, the end of a turn, a close.
- **verify**: check a record against its own links and its anchors.
  **replay**: rebuild each decision's request from the inputs it names, ask
  the core again, compare with the recorded answer.
- **divergence**: the first entry where a replayed decision differs.

## 2. Requirements

|Id|Requirement|
|---|---|
|T1|Complete. Every decision of the session engine and every effect appears in the record: a model request, a tool run, a file write, a program run, a message sent or delivered, a spawn, a question and its answer, a grant or a revoke, a settings change, a compaction. An effect's intent is acknowledged in the record before the effect starts; it never has two outcomes, and has exactly one once the session is open again after any crash.|
|T2|Attributed. Every entry names its author and its cause. Only a user's input, a schedule firing or the harness's start has no cause. Following causes from any entry reaches such an origin in finitely many steps: no effect without a user, a schedule or a parent behind it; no cycle.|
|T3|Ordered. Entries of one session have one order. Across sessions, a spawn precedes the child's first entry, a send precedes its delivery, a report precedes its placement. Time of day is an input like any other: no decision reads a clock that the record does not hold.|
|T4|Tamper-evident. Each entry is bound by a hash to all entries before it. Short of a collision of that hash, a record that differs in any entry (changed, removed, inserted, moved) from the one a head or an anchor was taken from fails verification against it, and a record cut short fails against any anchor taken after the cut. Verification names the first entry whose link or anchor does not hold. What was appended after the last anchor is evident only from the next anchor on.|
|T5|Crash-clean. After a crash at any point, what an open reads verifies, and holds every acknowledged entry. An anchor is taken only of acknowledged entries, so the unacknowledged tail that an open cuts is never reported as tampering.|
|T6|Replayable. Replaying a record gives every decision the answer the record holds, byte for byte, on the same core. A replay causes no effect and appends nothing. When a decision differs (another core, a changed record), the replay reports the first divergence: its place, the recorded answer, the new one.|
|T7|Inputs complete. Everything a decision read is in the record before the decision: no decision depends on a value the record lacks. A replay that misses an input says which and whether it was removed or redacted, and decides nothing in its place.|
|T8|The whole tree. A child's head is anchored in its parent's record at spawn and at each report, and a root's head in the daemon's ledger at each of its anchor points. Verifying a root verifies every record of its tree against its last anchor; a missing child record is reported as missing, a deleted one as deleted.|
|T9|Audit. One query over a tree answers: for an effect (a write to a path, a program run, a send to a host), which agent did it, by which decision, from which origin; and for an agent, every effect it caused. The answer is exactly the matching effect entries, each once, each with its agent, its decision and its origin, in an order that respects T3.|
|T10|No credential, and redaction keeps the proof. No credential value is in the record. An entry's content can be redacted to its digest: the content is gone, the record still verifies, every other entry is untouched, and a replay that needs it says it is redacted. Deleting a session writes a tombstone in its parent's record and in the ledger.|
|T11|Out of an agent's reach. A write or a delete by an agent that targets a record, an anchor or the ledger is refused, whatever the agent holds (`spec/security/SPEC.md` C11: they are part of the store). Reading another agent's record is a read like any other.|
|T12|Portable. An exported record verifies and replays with the released verifier alone, to the verdicts its source gives: no daemon, no network, no access to the machine it came from. Its format is versioned under `spec/contract/SPEC.md` W9.|

## 3. What exists

### eukhe (origin/merge/main-into-client-sdk)

|Area|What it gives today|Where|
|---|---|---|
|commit log|`main.jsonl`: append only, one commit per line, fsync per commit; an acknowledged commit survives any crash; open reads the complete lines and cuts a torn tail.|`bend/log.bend`, `spec/durable/log.bend`, `laws/log.bend` (D1), `crates/eukhe-durable/src/storage/jsonl/`|
|session tree|One tree holds a session's state; replaying its journal makes the tree again; a prefix is a snapshot.|`bend/tree.bend`, `laws/tree.bend`|
|intent before effect|A tool runs only for a call of a committed assistant entry; its intent is recorded before it executes; it settles once; an unsafe call never runs twice across a restart.|`spec/harness/effect.bend`, `laws/tool_call.bend` (H1)|
|versioned calls|Every stored tool call carries `family@rev`; an older call is lifted to the current rev; replay at the same rev is byte-stable.|`spec/harness/lift.bend`, `laws/call_lift.bend` (H3)|
|argument repairs|Each repair of a call's arguments is recorded once.|`laws/arg_repair.bend` (H2)|
|entries|An entry has an id, a kind, its conversation, the task that appended it; a user-role input carries its origin (user, goal, autonomous, director, quota resume, report).|`crates/eukhe-durable/src/types/transcript.rs:95`, `crates/eukhe-types/src/input_origin.rs`|
|usage|A child's usage is attributed into its parent with the row that spawned it.|`crates/eukhe-core/src/durable/children/registry.rs`|
|replays in small|The codemode sandbox replays its journal deterministically; the autoresearch store rebuilds its state from its log.|`crates/eukhe-durable/src/codemode/mod.rs`, `crates/eukhe-core/src/autoresearch/store.rs`|
|pure decisions|Every rule is a pure function of bytes (one C entry, ids never reused), so a decision is replayable once its request bytes are kept.|`bend/core_entries.txt`, `crates/eukhe-bend/WIRE.md`|

Gaps against the requirements:

1. Decisions are not entries. The core's requests and answers are not
   written, so the record shows what happened, not what was decided (T1, T6).
2. The request a model received is not recorded: it is rebuilt from the
   transcript by Rust (prompt assembly, quirks, scrubber) (T7).
3. An approval's answer is a transient frame, not an entry
   (`crates/eukhe-daemon/src/shell_approval.rs`): a refusal shows in the
   tool's result text, a yes shows nowhere. An agent's own settings changes
   are kept (the `eukhe.cvar.agent` document); a user's change of the
   settings files is not (T1).
4. No integrity beyond the torn tail: a line changed in the middle of
   `main.jsonl` reads as valid. No digest, chain or anchor; a search of the
   storage code for sha256, checksum or a previous-hash field finds none
   (T4, T8).
5. Causes are partial: `byTaskId` and the input origin exist; a tool
   result does not name the decision that allowed it; a child's first entry
   does not bind to the parent's spawn entry by digest (T2, T3).
6. No audit across sessions; each storage is read alone (T9).
7. Clock readings, generated ids and file contents that decisions read are
   not captured as inputs (T7).

### oh-my-pi (c28b3e3, paths under `packages/coding-agent/src` unless rooted)

|Behavior|Where|
|---|---|
|One JSONL file per session: header with `version` 3, then entries with `id`, `parentId`, ISO `timestamp`, `runtime` (the writer's build); 16 entry kinds.|`session/session-entries.ts:17,42-111,355`, `docs/session.md:42-122`|
|No request record: the reply is a `message` with provider, model, usage, stop reason; side calls are `model_usage`; the main session's system prompt is only a digest (`system-prompt-digest`).|`packages/ai/src/types.ts:1311-1399`, `session/session-entries.ts:119-135`, `session/session-tools.ts:291-305`|
|Tool call in the assistant message; a `tool_execution_start` entry just before the tool runs; the result as a `toolResult` message; large output spills to a numbered artifact file.|`session/agent-session.ts:3926-3938`, `packages/ai/src/types.ts:1056-1063,1401-1420`, `docs/blob-artifact-architecture.md:141`|
|Approval decisions are not in the session: grants live in memory or `approval-cache.db`.|`tools/approval-cache.ts:1-10,38`, `docs/approval-mode.md:37,45`|
|A subagent is its own file under the parent's stem; its `session_init` stores system prompt, task, tools, model; entries carry no agent id (the file implies it).|`task/executor.ts:4508,4864-4866,5206-5210`, `session/session-entries.ts:277-321`|
|No hash, chain or signature; not strictly append only (rewrites for migration, strip, sanitising); no fsync; malformed and torn records are skipped and dropped at the next rewrite.|`docs/session.md:506,543,614`, `session/session-loader.ts:170-181,354-380`|
|Images are content-addressed blobs (`blob:sha256:`); artifacts are not.|`session/blob-store.ts:8,45,60-67`, `docs/blob-artifact-architecture.md:76`|
|No replay: "replay" means resending history to the provider; `--restore` reruns cut-off turns with "outcome unknown" results; fork, branch and seance copy or read paths.|`packages/agent/src/replay-policy.ts:1-13`, `docs/session-operations-export-share-fork-resume.md:369-415,501`|
|Export: HTML with subagent transcripts (not redacted); `/dump` of the live request; an anonymised zip; OTLP spans (`invoke_agent`, `chat`, `execute_tool`) when an endpoint is set; a stats database and a hub that scans child files.|`docs/session-operations-export-share-fork-resume.md:60-124`, `telemetry-export.ts:79-95`, `packages/agent/src/telemetry.ts:74-116`, `docs/agent-hub.md:63-117`|
|Retention: `gc` archives and strips on request; `/delete` is "not a guaranteed erasure boundary".|`docs/session.md:601-618`, `docs/session-operations-export-share-fork-resume.md:625`|

omp has no behavior for: tamper evidence; a per-request record of the model
input; a record of approval decisions; deterministic replay; a per-entry
agent or user identity; an audit query across agents beyond the hub's scan.
Where omp has the behavior eukhe matches it already (entries, usage, child
transcripts, a start marker before a tool runs) and is stricter (fsync,
append only). T4 to T9 are designed, not ported.

## 4. Proposed laws (requirement laws only)

|Req|Law|States|Rejects|
|---|---|---|---|
|T1|`record_intent_before_effect`|In the world of one effect (commits, runs, crashes, aborts), an effect starts only after its intent entry is acknowledged; this extends `execute_after_committed` from tool calls to every effect kind.|A message sent, then logged.|
|T1|`record_outcome_once`|In every state a started effect has at most one outcome entry; after the next completed open it has exactly one (an effect a crash cut is settled as interrupted).|Two results after a retry; none after a restart.|
|T1|`record_decision_is_call`|The answer a decision entry holds is the rule's answer on the request it holds, and the host model acts only on an answer it recorded.|A decision logged after a fallback changed it.|
|T2|`attr_entry_needs_author_and_cause`|An append without an author, or with a cause that names no earlier entry, is refused and changes nothing.|Entries with a dangling cause accepted.|
|T2|`attr_origin_only_user_or_schedule`|An entry with no cause is accepted only when its author is a user or the harness's schedule or start.|A model reply or a tool output recorded as a causeless input, so the effects after it have no one behind them.|
|T2|`attr_reaches_origin`|From every entry of a verified tree, following causes ends at an origin within as many steps as the entry's place in the tree's merged order.|A cause that points forward, or at itself.|
|T3|`order_links_respected`|In the merged order of a tree's records, each record keeps its own order, a spawn precedes the child's first entry, a send precedes its delivery, and a report precedes its placement.|A merge by wall-clock time.|
|T4|`chain_honest_verifies`|Every record built by appends verifies against each head it had.|A verifier that rejects an empty or one-entry record.|
|T4|`chain_change_detected`|Two records with equal heads are equal (for a hash without collisions on them): so a record with any entry changed, removed, inserted or moved does not verify against a head or anchor of the original taken at or after that entry.|A check of the last link only; a chain over ids, not content.|
|T4|`chain_first_bad_exact`|The place verification reports is the first entry whose stored link differs from the digest of the entry before it, or whose position an anchor contradicts; it reports none exactly when there is none.|A verifier that always names the first entry, or the last.|
|T4|`chain_cut_fails_anchor`|A proper prefix of a record does not verify against an anchor taken after the prefix.|Truncation passing because every remaining link is valid.|
|T5|`chain_prefix_verifies`|Every prefix of a verified record verifies by itself; with the log's laws (`log_reads_lines`, `log_only_commits`), what an open reads after any crash verifies.|A chain whose last entry seals the whole file.|
|T5|`chain_ack_kept`|An acknowledged entry, with its link, is in what the next open reads (the log's `log_ack_durable` carried to entries).|A link kept in memory and written with the next entry.|
|T5|`anchor_only_acknowledged`|Every anchor is the head of acknowledged entries: for every crash, the record an open reads extends every anchor taken of it.|A parent that anchors a child's head before the child's last entry is durable.|
|T6|`replay_same_decisions`|For every run of the host model, the request rebuilt from the input entries a decision names equals the request that was decided, and the rule's answer on it equals the recorded answer.|A decision that reads a clock or a file the record lacks.|
|T6|`replay_no_effect`|In the host model, running a replay appends no entry and emits no effect action, for every record.|A replay that reruns a tool to fill a gap.|
|T6|`replay_divergence_exact`|When a replay reports a place, all decisions before it agree, the answers at it differ, `was` is the recorded answer and `now` the rule's answer there; when it reports none, all agree.|A replay that stops at the first input it cannot read and says "equal"; answers swapped.|
|T7|`replay_input_before_use`|Every input a decision entry names is an earlier entry of the record or an anchored entry of its parent.|A decision that names an entry appended after it.|
|T7|`replay_missing_is_named`|A replay over a record with an input removed answers "missing" with its place, with an input redacted "redacted" with its place, and in both cases no decision that needs it.|A default value used for a missing blob; a redaction reported as loss.|
|T8|`anchor_child_in_parent`|After a spawn and after each report, the parent's record holds the child's head at that moment; a tree verifies only when each child's record extends its last anchor.|A child rewritten after its report passing.|
|T8|`anchor_root_in_ledger`|After each anchor point of a root, the ledger holds its head; verifying a tree checks the root's record against the ledger's last head for it.|A daemon that never writes root heads, so a re-chained root verifies.|
|T8|`tree_missing_is_reported`|A tree with a child record absent verifies as "missing child", with a tombstone as "deleted", never as whole.|A walk that skips unreadable children.|
|T9|`audit_exact`|The audit's answer for a filter is exactly the effect entries of the tree that match it, each once, as a subsequence of the merged order.|A query that reads only the root; matches in file order.|
|T9|`audit_attribution_exact`|Each effect the audit returns carries the author of its intent entry, the decision entry its intent names, and the origin at the end of that entry's causes.|Every effect attributed to the root agent.|
|T10|`redact_keeps_chain`|Redacting an entry leaves the head and every other entry unchanged, and the record verifies.|A redaction that rewrites later links.|
|T10|`redact_hides_content`|After a redaction the entry's content is not readable from the record or its blobs, and a replay that needs it answers "redacted".|A redaction that only sets a flag.|
|T10|`record_holds_no_credential`|No value of the host's credential registry occurs in any entry content the host model appends (the exact values, not patterns).|A tool output that prints a key the patterns miss, stored raw.|
|T10|`delete_leaves_tombstone`|Deleting a session writes a tombstone for it in its parent's record and in the ledger before its files go; verification then reports "deleted".|A silent delete that later reads as "missing".|
|T11|`record_write_refused`|A write or delete by an agent whose real path is a record, an anchor or the ledger is refused for every set.|A broad write capability over the sessions directory.|
|T12|`export_round_trip`|Reading an export gives the record back, and it verifies to the same head.|An export that drops unknown entry kinds.|
|T12|`export_replays_same`|Replaying an imported export gives the verdict that replaying its source gives.|An export with digests but not the blobs a replay reads.|

Already proven and reused: D1 (`log_ack_durable`, `log_reads_lines`,
`log_only_commits`), H1 (`execute_after_committed`, `effect_once`,
`effect_settles_once`), H3 (`call_lift_replay_byte_stable`), the tree's
journal replay laws.

## 5. Core sketch

`bend/record.bend`, `bend/replay.bend`, `bend/audit.bend`:

```
type Kind:   Input{origin} | Decision{rule, inputs, answer} | Intent{effect} | Outcome{of, result}
type Entry:  Entry{seq, prev, author, cause, kind, body}      # body: digest of the content
type Head:   Head{len, digest}

append(record, draft) -> Maybe<(record, Head)>      # T1 T2
verify(record, anchors) -> Ok{head} | Bad{at, why}  # T4 T5 T8
redact(record, seq) -> record                       # T10
rebuild(record, decision) -> Request | Missing{at} | Redacted{at}    # T7
replay(record, call) -> Same | Diverged{at, was, now} | Missing{at} | Redacted{at}   # T6 T7
merge(records, links) -> order                      # T3
audit(tree, filter) -> effects with agent, decision, origin         # T9
```

`call` is the core's own dispatcher (entry id, request bytes), so a replay
is the same code that decided. The chain binds each entry to `prev`, the
digest of the entry before it; content lives in the commit line and in a
content-addressed blob store when large, so the record holds digests and
redaction is the removal of a blob. Rust keeps IO only: it writes each
decision at the one seam every rule call passes (`eukhe_bend::call`),
captures clock, ids and file digests as inputs, stores the request a model
received as its parts by reference plus one digest of the bytes sent, and
publishes anchors (child heads into the parent's commit, root heads into a
ledger file the daemon owns).

## 6. Surface

- Daemon and SDK: `record_get {sessionId, from, limit}`, `record_head`,
  `record_verify {sessionId, tree}`, `record_replay`, `audit_query {root,
  filter}`; every event carries the sequence of the entry it reports, so a
  client can tie what it shows to the record.
- CLI and TUI: `eukhe record verify|show|replay|audit`, `eukhe export
  --record`, a "why" view on any tool row (the decision, the capability, the
  user input behind it), a tree audit in the agents view.

## 7. Tests (with the implementation)

One per requirement, through the entries. Crash and restart: a kill between
intent and outcome, between an entry and its anchor, and in the middle of a
line; each reopened record verifies and holds the acknowledged entries.
Tamper: flip one byte, drop a line, swap two lines, cut the tail; each is
reported at the right place. Replay: every e2e session of the suite replays
to no divergence; a release gate replays a fixed corpus on the new core and
lists the decisions that changed. Real `claude-haiku-5-5` runs: a run with
two subagents is audited ("who wrote this file, from which message"), then
replayed with the network off.

## 8. Trust

Proven: the chain, the anchors, the replay's verdict, the audit's answer,
over the Bend model of a record and of the host's loop. Trusted: the hash
function (collisions), the Rust that captures inputs (a missed input shows
as a divergence in the replay tests, not in a proof), the file system under
the log's model. Tamper evidence holds against whoever cannot rewrite the
anchors, and for what was appended up to the last anchor: see questions 1
and 9.

## 9. Open questions for the user

1. Evident against whom? (a) Corruption and bugs: the chain alone. (b) The
   agent itself: records and ledger in the protected class, anchors held by
   the daemon. (c) The machine's own user or an administrator: a signing key
   outside the user's reach or an outside witness. Which is the target for
   the first version? The spec assumes (b).
2. How much is kept? Decisions with request digests and content by
   reference (assumed), or every request's full bytes? The second replays
   without the transcript and costs disk.
3. Which decisions: every rule call of the session engine (assumed), or
   only the gates (approval, admission, stop, capability)?
4. Replay scope: decisions only (assumed: exact and cheap). Should a
   release also be gated on replaying a corpus with the new core and
   reviewing every changed decision?
5. Retention and privacy: how long are records kept; is redaction to a
   digest enough for a deletion request; does a delete leave a tombstone
   (assumed) or nothing?
6. Sessions written before this pillar have no chain: start the chain at
   the upgrade with an "unverified prefix" marker (assumed), or rewrite
   them once?
7. Where is the hash computed: in Bend (the whole verifier is proven, slow
   path only) or in Rust (fast, trusted)? Assumed: Rust on append, Bend in
   the verifier.
8. One audit store for many sessions (an index the daemon keeps), or files
   only plus export (OTLP spans as omp has)?
9. How often is a root anchored in the ledger: at each turn's end, spawn,
   report and close (assumed), or at every commit? It is the window in
   which a rewrite of the newest entries would not show.
