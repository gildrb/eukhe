# contract (spec): the stable SDK contract

Status: spec only. Nothing below is implemented; no law named in section 4
exists yet. Ids `W1..W23` are provisional. W14 to W23 (one engine, two
doors) are planned like the rest.

A product built on eukhe does not break when eukhe is upgraded. The daemon's
wire protocol and the SDKs come with compatibility laws: versions that are
negotiated, unknown fields that are tolerated, an old client that works with
a new daemon and a new client that works with an old daemon, and rules for
taking anything away. The pillar builds on the daemon protocol and its
hello, the capability strings, the replacement verdict, the release version
laws, the versioned tool calls and `eukhe-client`; it adds what is missing: a
range of versions instead of one, a written schema with its history, a
checker that two schemas are compatible, and the laws that the checker is
right.

The SDK is one engine with two doors (section 2.1). The same core runs
either inside the host's process, as a library, or in the daemon; the host
uses one API for both and picks the door by configuration. Host tools,
approvals, budgets and cancellation are callbacks in both doors: called
directly in process, carried over the wire by a host-callback protocol
through the daemon. The compatibility laws apply to both doors.

## 1. Words

- **contract**: everything a product may rely on: the daemon wire (commands,
  responses, events, errors, their order), the stdio RPC mode, the durable
  formats a product may read (session storage, record export), the settings
  keys, the CLI's exit codes. Not the terminal UI.
- **frame**: one JSON line on the wire. **schema**: the written shape of
  every frame at one version. **history**: the schemas of every release,
  kept in the repository.
- **version**: `major.minor`. A minor adds; a major may remove. **range**:
  the versions one side speaks, lowest to highest.
- **capability**: a name in the hello for one optional feature. **feature**:
  a command, field or event that a version's schema has, or that a
  capability names.
- **critical**: a field whose silent loss would be unsafe. The frame says so
  itself: an object lists the names of its critical fields in its `critical`
  member. A field not listed there may be ignored by a receiver that does
  not know it; a listed one may not.
- **old client, new daemon**: a client built against an earlier release, in
  the window. **new client, old daemon**: the reverse.
- **window**: how long a release is served. A daemon speaks every version,
  of its own major and of earlier ones, that a release younger than the
  window spoke. The notice before a removal is at least the window, so a
  client built before a removal keeps speaking its own major until the
  window has passed.
- **lift**: read a value of an older schema as the newer one. **project**:
  read a value of a newer schema as the older one sees it.
- **host**: the program that uses the SDK. **frontend**: any client
  attached to a daemon session: a host, the terminal UI, the dashboard, the
  Signal gateway, an ACP editor.
- **door**: where the engine runs for a host. **In process**: the engine is
  a library in the host's process. **Daemon**: the engine runs in the eukhe
  daemon and the host reaches it over the daemon socket.
- **host callback**: a function the host gives the SDK and the engine
  calls: a host tool, an approval, a budget question. A **host call** is
  one such call; it ends in one **outcome**.
- **host id**: a name the host chooses for itself, the same across its
  restarts, under which it registers its callbacks with a daemon session.
  **grace**: how long a daemon session keeps a call pending for a host that
  detached.
- **hand-off**: moving an idle session from one door to the other.

## 2. Requirements

|Id|Requirement|
|---|---|
|W1|One written contract. Every frame the daemon sends or accepts is described by one schema with a version, and on a connection every frame the daemon emits is valid in the schema of the agreed version. The Rust wire types, every SDK and the compatibility checks come from that schema.|
|W2|Negotiation. The daemon's hello states the range it speaks and its capabilities; the client states its range. The connection speaks the highest version in both ranges. With none in common, both sides get one typed error that carries both ranges as stated and says which side is too old; never a hang, a guess or a half-open connection.|
|W3|Old client, new daemon. A client built against any release in the window works with every later daemon whose range holds its version: the daemon reads its commands and writes its responses and events by the schema of the agreed version; each command means what it meant; each response and event it understands arrives with the fields it knew, unchanged in meaning.|
|W4|New client, old daemon. A client works with every daemon in the window: for each feature the daemon has, as above; a feature the daemon lacks (the agreed version does not have it, or the hello does not list its capability) is not sent: the product gets one typed "not supported by this daemon" error instead.|
|W5|Minors only add. Within a major a release may add a command, an optional field, an event, an enum value, an error code, and each such addition is accepted. Never a field, command, event or code removed or renamed, a type changed, an optional field made required, a default changed, or a stated order guarantee dropped.|
|W6|Unknown is tolerated. A receiver ignores a field it does not know, unless the frame lists it as critical (W7), and keeps it when it stores or relays the object. An event of an unknown kind is skipped: its sequence number still counts and no gap is reported. An unknown enum value reads as "unknown" with its text, never as an error and never as a known value. An unknown command gets a typed error with its id, and the connection stays usable.|
|W7|Critical is never ignored. A sender lists in the frame each field whose silent loss would be unsafe. A receiver refuses whole, with nothing done, a frame that lists a field it does not know; the same frame without that field is treated as any other.|
|W8|Deprecation. A feature is removed only at a major, and only after every release of the notice period marked it deprecated; a history that does so is accepted. The mark changes nothing else. A client that uses a deprecated feature is told exactly once per connection and feature what replaces it and at which version it goes.|
|W9|Durable formats. A build reads every format an older build of the window wrote: every field the older format held reads back with the value it had. A file of a newer format than the reader understands is refused untouched, with both versions named: never half-read, never rewritten.|
|W10|Errors and order are part of the contract. Error codes are stable names; their text is not. Every command gets exactly one response with its id. Per session, event sequence numbers rise by one, and a gap is marked.|
|W11|SDKs. Each official SDK is generated from the schema, states the range it speaks, and works with any daemon whose range meets it. Process rule, no law: an SDK's own major changes only when its API breaks.|
|W12|Upgrade is safe. Replacing a daemon by a newer build never ends a session's work: only an idle daemon is replaced. After it, an attached client of an older build either still has a version in common and its next command is answered, or receives the typed error of W2; never a silent close.|
|W13|Proven by a matrix. Process rule, no law: each release is tested against the clients and daemons of every release in the window, both ways, before it ships; a release that breaks one is not released.|

### 2.1 One engine, two doors (planned)

User decision (2026-11-11): one engine, two doors, one API. In process, the
host gets simplicity and its own tools as plain functions. Through the
daemon, it gets sessions that survive its crashes and restarts, several
frontends on one session, and isolation. Switching is a change of
configuration. Nothing in this subsection is built.

|Id|Requirement|
|---|---|
|W14|One API, two doors. The SDK has one API for both doors. The host chooses the door with one connect option: in process with its agent dir, or a daemon socket, given or resolved as the `eukhe` CLI resolves it. Every call, argument, result type and typed error is the same in both doors (W20 names the only answers that differ); a host program changes doors by changing that option and nothing else.|
|W15|One event stream. Both doors deliver the same events: the wire's session event vocabulary, with the same per-session cursor (generation, sequence), the same start snapshot, the same order and the same gap marks (W10). For one scripted run on a fixed clock, the streams of the two doors are equal. No engine type is part of the API.|
|W16|Host callbacks in both doors. Host tools, approvals, budget questions and cancellation are given once, as the same callbacks, whichever door is chosen. In process the engine calls them directly; through the daemon the host-callback protocol (W17) carries the same calls. In both doors a callback receives the same arguments, and its answer has the same effect on the session.|
|W17|Host-callback protocol. Through the daemon, a host registers its callbacks for a session under its host id: each tool with its name and parameter schema, and the kinds of question it answers. The daemon sends a call frame with a call id; for a tool the host may send progress, and it answers once with that id. Each call ends in exactly one outcome: the host's answer, a cancellation (sent to the host as a cancel frame for the id), or `host_gone` (W18). An answer for a call that already ended is dropped. A tool name that is an eukhe tool or another host's tool is refused at registration, and the refusal changes nothing. The frames are in the schema (W1) and follow its rules (W5 to W7).|
|W18|A daemon session outlives its host. When a host detaches, the session keeps running. A call pending to that host stays pending for the grace the host stated when it registered. When the same host id attaches again and registers the callback within the grace, it receives each pending call again with its original id, so it can tell a repeat from a new call. After the grace the call ends `host_gone`: a host tool returns a tool error, an approval is a denial, a budget question adds nothing. With several frontends, a tool call goes to the host that registered the tool; an approval or a budget question goes to every attached frontend that answers that kind, and the first answer wins, as the approvals of G5 do today.|
|W19|Cancellation means the same in both doors. Every SDK call takes the host's cancellation token. Cancelling it ends that call: the run a prompt started is aborted as the abort command aborts it, a wait returns cancelled, and work the call did not start is not touched. Closing a connection to a daemon cancels nothing (W18). Closing an in-process session ends its work, since nothing outlives the host's process there.|
|W20|The door changes lifetime and sharing, not meaning. The daemon door adds what a separate process gives: sessions that survive the host's crash and restart, several frontends on one session, and isolation from the host's process. An operation that needs one of these (attach to a session another process hosts, list resident sessions, messages and scheduling between sessions) answers one typed `needs_daemon` error in process, decided before any effect. `supports(feature)` answers in both doors.|
|W21|Hand-off at rest. A session started in process can be handed to a daemon, and a daemon session can be taken into a process, when it is idle and its storage is durable. The handing side stops the engine and releases the session's lease; the receiving side opens the same storage under its own lease. The host's handle keeps working: the same session id, the event cursor continuing with no gap and no repeat, the host's callbacks registered again on the new side. A running session is refused with `session_busy`, a session in memory with `not_durable`, a daemon session with another frontend attached with `session_shared`; a refusal changes nothing. A run in flight never moves between processes, and no two processes hold one session's storage at the same moment.|
|W22|Compatibility laws apply to both doors. Through the daemon the SDK is a client like any other: W2 to W4, W6 to W8, W10 and W12 hold for it, the host-callback frames included. In process the SDK and the engine are one build, so nothing is negotiated, but the SDK's API follows W5 and W8 (a minor only adds; a removal waits for a major and its notice), and a session written in process follows W9, which is what makes a hand-off between builds safe.|
|W23|Proven the same. Process rule, no law: one host program, run against both doors on the same scripted model, gives equal event streams and equal calls to its callbacks; a release where they differ is not released.|

Why hand-off only at rest: a run in flight holds a kernel process, open
provider streams and tool calls in progress, and none of them can move to
another process. An idle session is what its durable storage holds, and a
daemon worker already opens a session from its storage when it resumes one.
A refusal the host can wait out is safer than a move that loses or repeats
an effect.

## 3. What exists in eukhe

### eukhe (origin/merge/main-into-client-sdk)

|Area|What it does today|Where|
|---|---|---|
|daemon protocol|JSONL frames; `eukhe.daemon` version 7, schema revision 30, a schema id string; the wire types are hand-written Rust, with payloads of other subsystems as opaque JSON.|`crates/eukhe-types/src/daemon/mod.rs:1-30`|
|hello|The hello carries the protocol, the app version, the build id, the capabilities; capability strings are open on the wire; `idle_shutdown` exists because a daemon without it would read `shutdown {ifIdle}` as an unconditional shutdown.|`crates/eukhe-types/src/daemon/mod.rs:24-37`, `crates/eukhe-daemon/src/protocol.rs:199-232`|
|envelope check|A command must be an envelope naming `eukhe.daemon` and a version. The lowest accepted version equals the daemon's own: the daemon accepts exactly one version; older gets "protocol too old", newer "the client is newer than the daemon".|`crates/eukhe-daemon/src/protocol.rs:20,277-322`|
|client|`eukhe-client` sends the lower of the daemon's and its own version; the CLI refuses a command when the daemon's protocol is below its own.|`crates/eukhe-client/src/daemon_client.rs:578-592`, `crates/eukhe-cli/src/daemon_command.rs:193-201`|
|unknown input|An unknown command type is a typed error; unknown fields are ignored because no wire type denies them (serde's default), stated nowhere.|`crates/eukhe-daemon/src/protocol.rs:273-285`|
|replacement|Only an interactive start replaces a daemon, only an idle one of a lower version; a newer daemon or another build is kept and the user is told. This, not a version range, is how versions meet today.|`bend/replace.bend`, `laws/replace.bend`, `bend/launcher.bend`, `crates/eukhe-client/src/daemon_build.rs`|
|tests across versions|Mock daemons of other versions: an idle older daemon is replaced, a busy one kept, an older client keeps a newer daemon or exits with its message on another schema, a foreign protocol is replaced.|`crates/eukhe-cli/tests/daemon_replacement_e2e.rs:470-660`|
|events|A cursor (generation, sequence); a resume that is not at the end answers `event_replay_not_available`.|`crates/eukhe-daemon/src/protocol.rs:420-447`|
|other surfaces|`--mode rpc` (stdio JSONL); ACP; the dashboard's own bridge protocol 3 with an allow list of daemon commands (a new command runs nowhere until listed).|`crates/eukhe-daemon/src/rpc/mod.rs`, `crates/eukhe-dashboard/src/protocol.rs:15`, `bend/dash_policy.bend`|
|durable formats|Tool calls carry `family@rev` and are lifted; legacy `<id>.jsonl` sessions are imported once.|`laws/call_lift.bend` (H3), `bend/staging.bend`|
|versions|Release numbers and their order are proven; the Bend core's wire and entry ids never change meaning.|`bend/semver.bend`, `bend/wire.bend`, `bend/core_entries.txt`|
|SDKs|`eukhe-client` (Rust, the wire client), `eukhe-sdk` (Rust, in process: it re-exports the engine's own types). No generated schema, no client in another language.|`crates/eukhe-client/src/lib.rs`, `crates/eukhe-sdk/src/lib.rs`|

Gaps against the requirements:

1. No range: a daemon speaks one version, so an older client and a newer
   daemon meet only by replacement, and a product pinned to an SDK breaks
   at the next protocol bump (W2, W3, W4).
2. No written schema and no history: the contract is the Rust types of
   this commit; nothing checks a change against the last release (W1, W5).
3. Tolerance is an accident of serde, not a rule; whether a relayed or
   stored object keeps unknown fields is not stated (W6).
4. One feature is capability-gated (`idle_shutdown`); there is no general
   rule for a field that must not be ignored (W7).
5. No deprecation rule (W8). No rule for a file written by a newer build
   (W9).
6. The in-process SDK exposes engine types, so every engine change is an
   API change (W11, W14).
7. The tests use mocks of other versions, not released builds or recorded
   frames (W13).

### Two doors today

|Door or surface|What it does today|Where|
|---|---|---|
|`eukhe-sdk` (in process)|`open_session`, `prompt`, `watch`, `available_models`, `new_session_id`; the rest is the engine's own types re-exported: `EukheSession`, `SessionConfig`, `Conversation`, `AgentEvent`, `Models`, and the `Context` of `eukhe-chord`. Its doc says a change to any re-exported type breaks the facade.|`crates/eukhe-sdk/src/lib.rs:1-66`|
|`eukhe-client` (daemon)|The wire client: the supervisor connection and its hello, requests matched by id, the event stream, the direct link to a worker, the launcher that starts a daemon, the saved-session catalog with the create and attach requests. It shares no type with `eukhe-sdk`: a host that moves from one to the other rewrites its code.|`crates/eukhe-client/src/lib.rs:1-34`|
|`--mode print`, `--mode json`|In process; the session closes when its runs settle.|`crates/eukhe-cli/src/mode.rs:56-67`, `crates/eukhe-cli/src/print_runtime.rs:87-96`|
|`--mode rpc`|In process: stdio JSONL over one durable session. Scheduling and agent messaging answer "requires daemon mode", and `observe` sees no other session.|`crates/eukhe-daemon/src/rpc/mod.rs:1-19`, `crates/eukhe-daemon/src/rpc/error.rs:130`, `crates/eukhe-cli/src/print_runtime.rs:125-133`|
|`--mode acp`|Through the daemon: makes sure a supervisor runs (never replacing one), creates the daemon session the flags select, and serves ACP over it.|`crates/eukhe-cli/src/print_runtime.rs:148-183`|
|terminal UI|Through the daemon, starting a supervisor when none runs.|`crates/eukhe-cli/src/print_runtime.rs:97-106`|
|events|In process: the engine's `AgentEvent` batches, one per commit, after a start snapshot, with no sequence number. Through the daemon: `SessionEvent`, which the worker projects from the engine's events once; the TUI, the gateway, ACP and the RPC mode all read this vocabulary.|`crates/eukhe-sdk/src/lib.rs:108-166`, `crates/eukhe-types/src/daemon/session_event.rs:1-24`, `crates/eukhe-daemon/src/worker/durable_host/translator.rs`|
|host tools|None in either door. A session's extensions are a fixed list and its roster is fixed after them; `SessionConfig` has no field for a host's tools. Through the daemon, the MCP servers an ACP client names are the only way in for outside tools.|`crates/eukhe-core/src/durable/registry.rs:28-94`, `crates/eukhe-daemon/src/acp/mcp.rs:365`|
|approvals|In process: `SessionConfig::shell_approval`, a callback for the gated steps of `bash` (G5); without it every gated step is denied. Through the daemon: the `shell_approval` event and the `answer_shell_approval` command under the `shell_approval` capability; the first answer of an attached client wins, and with no client attached the question goes to the parent session.|`crates/eukhe-core/src/durable/deps.rs:225-236,308-310`, `crates/eukhe-types/src/daemon/outbound.rs:331-350`, `crates/eukhe-types/src/daemon/command.rs:670`|
|other host requests|`SessionConfig::extra_host_handlers`: kernel host requests the embedding serves (the daemon's message and observe bridges). In process only.|`crates/eukhe-core/src/durable/deps.rs:295-298`|
|cancellation|In process: the `Context` every engine call takes. Through the daemon: the abort commands (`abort`, `abort_bash`, `cancel_rlm_child` and others), which act on the session.|`crates/eukhe-sdk/src/lib.rs:44-46`, `crates/eukhe-types/src/daemon/command.rs:566,653,751`|
|budgets|No host budget callback in either door; the budgets pillar is in work and not landed.|none|
|one owner per session|A lease per session file: one process hosts one runtime per session, and stale owners are reclaimed. The CLI's headless session and the daemon take it; `eukhe-sdk` does not.|`crates/eukhe-daemon/src/lease.rs:1-9`, `crates/eukhe-cli/src/headless_session.rs:3,24`|

Gaps against W14 to W23:

8. Two APIs: `eukhe-sdk` and `eukhe-client` share no type, so changing
   doors is a rewrite (W14).
9. Two event vocabularies. The in-process stream has no cursor, and the
   projection to `SessionEvent` lives in the daemon worker only (W15).
10. No host tools in either door. Approvals are a callback in process and
    frames on the wire, and nothing makes them one API (W16, W17).
11. No rule for a host that detaches with a call pending: no host id, no
    grace (W18).
12. In process the `Context` is the only cancel; through the daemon the
    abort commands act on the session, not on the call that started the
    work (W19).
13. No typed `needs_daemon` in the SDK; the RPC mode has its own messages
    for it (W20).
14. No hand-off, and the in-process SDK takes no lease, so nothing stops a
    host and a daemon from opening one session at once (W21).
15. Nothing compares the two doors (W23).

## 4. Proposed laws (requirement laws only)

"Dispatch model" and "client model" are the Bend models of the daemon's
and the client's loop over one connection: the frames an adversary sends
and the frames each emits.

|Req|Law|States|Rejects|
|---|---|---|---|
|W1, W3|`dispatch_speaks_agreed_schema`|On a connection that agreed a version, the dispatch model decodes each command by that version's schema, and every frame it emits is valid in it.|A daemon that agrees an old version and answers in its newest shapes.|
|W2|`proto_agree_highest_common`|The negotiated version is the highest one in both ranges; there is none exactly when the ranges do not meet.|The client's highest taken without the daemon's range; the lowest common version.|
|W2|`proto_refusal_exact`|With no common version, the answer is "client too old" exactly when the client's highest is below the daemon's lowest, else "daemon too old", and it carries both ranges as they were given.|Today's message telling a newer client it is too old; ranges swapped.|
|W3|`compat_old_frame_same_meaning`|When the checker accepts (old, new), every frame valid in old is valid in new and lifts to the same value with the new fields absent.|A checker that compares field names only and misses a type change.|
|W3|`compat_chain_sound`|When the checker accepts each consecutive pair of a history, a frame valid in its first schema is valid in its last and lifts to the same value: checking each release against the one before covers the window.|Harmless steps that together change a meaning.|
|W4|`compat_new_frame_projects`|When the checker accepts (old, new), a frame valid in new, of a kind old knows and listing no critical field old lacks, read by old's reader, gives the new value's projection onto old's fields: each old field unchanged.|A new required field old readers cannot fill; an enum value that old maps onto a known one.|
|W4|`feature_sent_only_when_present`|The client's send decision answers "send" exactly when the agreed version's schema has the feature and, where a capability names it, the hello lists that capability; else "not supported", and the client model sends nothing.|Send first and pass on `unknown_command`.|
|W5|`compat_rejects_breaks`|The checker refuses a pair in which a field, command, event or error code of old is missing in new, has another type, became required, changed its default, or in which an order guarantee of old is missing.|A checker that accepts a rename.|
|W5|`compat_accepts_additions`|The checker accepts a pair that differs only by a new command, optional field, event, enum value or error code.|A checker that refuses everything.|
|W6|`decode_ignores_unknown`|For an object with extra fields that it does not list as critical, the decoded value equals the value decoded without them.|A reader that fails on a field it does not know.|
|W6|`relay_keeps_unknown`|Encoding what the keeping decoder read gives back every field, the unknown ones included.|A daemon that stores a client's object and drops what it did not know.|
|W6|`decode_unknown_value_marked`|An enum text not in the schema decodes to "unknown" with that text, and to no listed value.|A fallback to the first variant.|
|W6|`dispatch_unknown_command_typed`|An unknown command gets the error `unknown_command` with its id, and the dispatch model's state is unchanged.|A dropped connection; a reply with no id.|
|W6|`stream_unknown_kind_skipped`|The client model, given a stream that holds events of unknown kinds, delivers the known events in order and reports no gap.|A client that fails on the event, or skips it and then reports a gap.|
|W7|`critical_unknown_refused`|A frame that lists as critical a field the receiver does not know is refused whole and the state is unchanged; when the frame without that field is valid, that one is accepted.|`ifIdle` ignored and the daemon stopped.|
|W8|`removal_needs_notice`|The history checker refuses a removal that is not at a major, or that some release of the notice period did not mark deprecated.|A field deprecated and removed in one release.|
|W8|`history_accepts_noticed_removal`|The history checker accepts a history whose only removals are at a major after a full notice period of marks.|A checker that refuses every history.|
|W8|`deprecated_told_once`|Over any run of the dispatch model, a connection that uses a deprecated feature gets exactly one notice for it, carrying the replacement and the removal version the history states.|No notice; a notice on every command.|
|W9|`format_reads_older`|Reading a file of an older format and projecting the result onto that format's fields gives the values the file holds, as that format's description states them.|A migration that drops a field older files had.|
|W9|`format_newer_refused`|A file of a format above the reader's is refused, its bytes are unchanged, and the refusal carries the file's version and the reader's.|A reader that accepts a newer version silently.|
|W10|`one_response_per_command`|For every order of commands and events, each command id gets exactly one response.|A timeout and a late reply both sent.|
|W10|`event_seq_gapless`|Per session, what a client receives is events with sequence numbers rising by one, or a marked gap (shared with orchestration O13).|A reconnect that restarts the sequence.|
|W12|`upgrade_answers_or_tells`|For a client of any range attached across a replacement, either negotiation with the new daemon agrees and its next command is answered, or it receives the error of `proto_refusal_exact`.|A connection closed with no reason.|
|W14, W20|`door_needs_daemon_before_effect`|In the in-process door model, an operation that needs the daemon answers `needs_daemon` with the state unchanged; every other operation answers what the daemon door model answers from the same state.|An in-process door that starts the work and then fails; one that refuses an operation the daemon would serve.|
|W15|`door_stream_equal`|For any sequence of engine commits, the events the in-process door model delivers equal those the daemon client model delivers for the same commits: kinds, cursors and gap marks.|In-process events without a sequence number; a door that merges batches and loses a gap mark.|
|W17|`hostcall_one_outcome`|In the host-call model, over any interleaving of answers, progress, cancels, detaches, attaches and grace expiries, each call id ends with exactly one outcome, and an input for an ended call changes nothing.|A late answer applied after a cancel; a call both cancelled and answered.|
|W17|`hostcall_name_unique`|Registration refuses a tool name held by an eukhe tool or by another host id, and a refused registration leaves the state unchanged.|A host tool that shadows `bash`; two hosts serving one name.|
|W18|`hostcall_redeliver_same_id`|A host id that registers again within the grace receives each of its pending calls exactly once more, with the original id; after the grace a call ends `host_gone` and is never sent again.|A reattached host that gets a new id for an old call; a call sent after it ended.|
|W18|`hostgone_safe_default`|`host_gone` ends a tool call with an error result, an approval with a denial, and a budget question with no addition.|An approval that times out into "allow".|
|W19|`cancel_scoped_to_call`|Cancelling one call's token aborts the run that call started and nothing else; a detach aborts nothing.|A host crash that aborts the session's run; a cancel that clears another frontend's queued prompt.|
|W21|`handoff_at_rest_only`|A hand-off succeeds only from an idle session with durable storage and, out of a daemon, no other frontend attached; otherwise it is refused with its reason and the state is unchanged.|Moving a running turn; a refused hand-off that already released the lease.|
|W21|`handoff_single_owner`|In the lease model, at every step of a hand-off at most one process holds the session's lease, and after a success the receiving side holds it.|The daemon opening before the process released; a release with no reopen that leaves the host a dead handle and no error.|
|W21|`handoff_cursor_continues`|The first event after a hand-off carries the sequence number after the last one before it.|A stream that restarts at zero; the last event sent twice.|

W12's first clause is already proven: the replacement and idle-shutdown
laws (`laws/replace.bend`, `laws/launcher.bend`) and the resume law of
tasks (D3). W11's second sentence and W13 are process rules: the schema is
generated and committed, the SDKs are generated from it, and the matrix
runs before a release (section 7).

W14 and W23 are tested, not proven. That the two doors expose one API is a
matter of Rust types (one API, two implementations behind it), and that
they behave the same is the test of section 7. The laws of the two doors
cover the models where they could differ: the host calls, the hand-off and
its lease, and the in-process refusals.

## 5. Core sketch

`bend/proto.bend` and `bend/schema.bend` (plain calls):

```
type Range:   Range{lo, hi}                         # versions as (major, minor)
type Agreed:  Speak{v} | ClientTooOld{client, daemon} | DaemonTooOld{client, daemon}
negotiate(client: Range, daemon: Range) -> Agreed                   # W2
may_send(agreed, hello, feature) -> Send | NotSupported             # W4

type Ty:      Str | Num | Bool | List{of} | Obj{fields, open} | Enum{values} | Any
type Field:   Field{name, ty, required, since, deprecated}
type Schema:  Schema{version, commands, responses, events, errors, guarantees}
compatible(old, new) -> Ok | Break{where, why}                       # W3 W4 W5
history_ok(list of Schema, window) -> Ok | Break{where, why}         # W8
decode(schema, json) -> Ok{value, kept} | Refused{why}               # W6 W7; kept: the unknown fields
dispatch.step(conn, frame) -> (conn, frames)                        # W1 W6 W8 W10
```

The laws tie `compatible` (the code: a structural walk over two schemas) to
what it promises (the spec: for every frame, lift and project), so the
checker cannot be wrong in a way the laws do not catch. Rust keeps IO only:
the schema is generated from the wire types of `eukhe-types` and committed
under `schema/history/<version>.json` at each release; CI runs
`history_ok` on the history and `compatible` on the working tree against
the last release; the daemon's dispatch and `eukhe-client` call `negotiate`
and `decode`; the SDKs for other languages are generated from the same
file. The dashboard bridge and the RPC mode get their own schema files
under the same checker.

The two doors add `bend/hostcall.bend` and `bend/handoff.bend` (plain
calls):

```
type Kind:     Tool{name} | Approval | Budget
type Outcome:  Answered{value} | Cancelled | HostGone
type Input:    Register{host, names, grace} | Answer{id, value} | Progress{id}
             | Cancel{id} | Detach{host} | Attach{host} | Tick{now}
hostcall.step(calls, input) -> (calls, frames)                       # W17 W18 W19
register(held, host, names) -> Ok{held} | Taken{name}                # W17
gone_default(kind) -> Outcome                                        # W18
door_gate(door, op) -> Run | NeedsDaemon                             # W20
handoff(session, lease, from, to) -> Moved{lease, cursor} | Refused{why}   # W21
```

In Rust, `eukhe-sdk` gets one session API with two implementations. The
in-process one wraps `open_session`, takes the session lease, and runs the
projection to `SessionEvent` that the daemon worker runs today, moved out
of `eukhe-daemon` so that both doors call one function. The daemon one
wraps `eukhe-client`. The host's callbacks are one `Host` value. In process
it becomes an extension of host tools installed before the roster is
fixed, the `shell_approval` sink, and the budget gate's question; through
the daemon the SDK registers it and serves the call frames with the same
functions.

## 6. Surface

- Hello: `protocol {name, lo, hi}`, `schema {id, version}`, `capabilities`,
  `deprecations [{feature, since, removal, use}]`. Client: `protocol {lo,
  hi}` in its first envelope. Errors: `protocol_no_common_version`,
  `unknown_command`, `not_supported`, `critical_unknown`.
- CLI: `eukhe daemon protocol` (ranges, capabilities, deprecations in use by
  attached clients), `eukhe schema check <old> <new>`, `eukhe schema print`.
- SDK: `client.protocol()` (the agreed version), `client.supports(feature)`,
  a deprecation callback.
- Two doors, SDK (Rust; names provisional):
  ```
  let eukhe = Eukhe::connect(Connect::InProcess { agent_dir }).await?; // or Connect::Daemon { socket: None }
  let host = Host::new("my-app").tool(my_tool).approve(my_approval).budget(my_budget);
  let session = eukhe.open(options, host, cx).await?;
  let mut events = session.watch(cx).await?;
  session.prompt("Summarize README.md", cx).await?;
  session.hand_off(Connect::Daemon { socket: None }, cx).await?;
  ```
  `Connect` is a value the host reads from its own configuration;
  `Connect::Daemon { socket: None }` resolves the socket as the CLI does
  (`EUKHE_DAEMON_SOCKET`, else the per-user default).
- Two doors, wire: commands `host_register {hostId, tools, answers,
  graceMs}`, `host_call_progress`, `host_call_answer`; events `host_call`,
  `host_call_cancel`, `host_call_ended {id, outcome}`; errors
  `needs_daemon`, `host_tool_name_taken`, `session_busy`, `not_durable`,
  `session_shared`; capability `host_callbacks`. `answer_shell_approval`
  stays (W5) and becomes one way to answer an approval call.

## 7. Tests (with the implementation)

One per requirement, through the entries. The matrix (W13): for each
release in the window, its recorded client frames are replayed against the
new daemon and the answers compared with the recorded ones on the fields
that release knew; and the new client runs against each released daemon
binary. Crash and restart: a daemon replaced in the middle of a client's
session; the client reattaches and its next command works. Formats: every
session storage of the corpus opens; a storage stamped one version ahead is
refused and its bytes are unchanged. Real `claude-haiku-5-5` run: the
previous release's client drives a full turn with a subagent on the new
daemon.

Two doors: one host program with a host tool, an approval and a budget
question runs against both doors on the faux model, and the event streams
and the calls its callbacks received are compared (W23). The host process
is killed during a host tool call and restarted under the same host id:
within the grace it receives the call again with the same id, and after the
grace the model sees `host_gone`. The terminal UI attaches to the host's
daemon session and both see one stream. Hand-off: an idle in-process
session with on-disk storage is handed to a daemon and goes on there with
no gap in the cursor; a running one is refused and keeps running; a host
and a daemon that open one session at once get one lease between them.
Real `claude-haiku-5-5` run: one turn that calls a host tool, through each
door.

## 8. Trust

Proven: negotiation, the checker against its meaning, tolerant decoding,
the history rule, the dispatch and client models. Trusted: that the
committed schema is what the Rust types serialise (a generated file with a
staleness test), JSON parsing, the released binaries used by the matrix.
Not covered by any proof: meaning that no schema states (what a command
does); the matrix tests that.

For the two doors, proven: the host-call model, the hand-off and its lease,
the in-process refusals. Trusted: that both doors call the one projection
function, and the SDK's mapping of a `Host` onto an extension and onto
frames; the test of W23 covers both.

## 9. Order to build the two doors

Everything here is planned. Steps 1 to 3 need no schema and can start
before W1; step 4 needs W1 and W2, because its frames enter the schema as
additions.

1. One API in process. `eukhe-sdk` gets its own `Eukhe`, `Session`,
   `Events` and error types; `watch` delivers `SessionEvent` with a cursor,
   from the projection moved out of the daemon worker; the in-process door
   takes the session lease. The engine re-exports go (W14, W15, gap 6).
2. Host callbacks in process. A `Host` value: host tools installed as an
   extension before the roster is fixed, their names checked against
   eukhe's tools; approvals through the `shell_approval` sink; cancellation
   through `Context`; the budget question once the budgets pillar has
   landed (W16, W19).
3. The daemon door. The same API over `eukhe-client`: create and attach,
   `SessionEvent` from the wire, cancellation as the abort of the run the
   call started, approvals over today's `shell_approval` frames;
   `needs_daemon` and `supports` (W14, W19, W20).
4. The host-callback protocol. Its Bend model and laws first, then the
   frames, the host id, the grace and the daemon's routing of calls to
   frontends (W17, W18). Host tools and budget questions then work through
   the daemon.
5. Hand-off, both ways, at rest, with its model and laws (W21).
6. The two-door test, and the matrix entries for the host-callback frames
   (W22, W23).

Step 1 changes the in-process API once, before anything is promised about
it, so it should land before the contract starts (question 3).

## 10. Open questions for the user

1. The window: which older clients must a new daemon serve (the previous
   major, every release of the last N months, everything since 1.0)? And
   how long is the deprecation notice?
2. What is "the SDK"? Decided on 2026-11-11: the in-process `eukhe-sdk` is
   part of it, with its own API, the same over both doors (W14 to W23).
   Still open: generated clients for TypeScript and Python as well?
3. When does the contract start: is protocol 7 frozen as 1.0 now, or after
   the other pillars have added their commands?
4. Which surfaces are in: the daemon wire (assumed), the stdio RPC mode,
   ACP, the dashboard bridge, session storage, the record export, settings
   keys, CLI flags and exit codes, tool names and schemas?
5. Version shape: `major.minor` (assumed, with today's schema revision as
   the minor) or one number plus capabilities?
6. With a window, a newer client can use an older daemon. Does an
   interactive start still replace an idle older daemon (assumed: yes), and
   what does it do with a busy one (assumed: use it)?
7. Known fields of the wrong type from a third-party client: refuse the
   frame (assumed) or coerce?
8. A session written by a newer build, opened by an older one: refuse
   (assumed) or open read-only?
9. The matrix: keep released binaries for the window (exact, heavy) or
   recorded frames per release (light, assumed for clients) or both?
10. The grace for a detached host: set by the host, with which default and
    which maximum (assumed: the default `--wait-limit-ms`, one hour, for
    both)?
11. May a frontend that did not start a session register host tools on it
    under its own host id (assumed: yes, if the names do not collide)?
12. Should a budget question go to every frontend that answers budget
    questions, first answer wins, as approvals do (assumed), or only to the
    host that set the limit?
