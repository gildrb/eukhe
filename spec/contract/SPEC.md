# contract (spec): the stable SDK contract

Status: spec only. Nothing below is implemented; no law named in section 4
exists yet. Ids `W1..W13` are provisional.

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

## 3. What exists

### eukhe (origin/merge/main-into-client-sdk)

|Area|What it does today|Where|
|---|---|---|
|daemon protocol|JSONL frames; `eukhe.daemon` version 7, schema revision 30, a schema id string; the wire types are hand-written Rust ported from the TS daemon protocol, with payloads of other subsystems as opaque JSON.|`crates/eukhe-types/src/daemon/mod.rs:1-30`|
|hello|The hello carries the protocol, the app version, the build id, the capabilities; capability strings are open on the wire; `idle_shutdown` exists because a daemon without it would read `shutdown {ifIdle}` as an unconditional shutdown.|`crates/eukhe-types/src/daemon/mod.rs:24-37`, `crates/eukhe-daemon/src/protocol.rs:199-232`|
|envelope check|A command must be an envelope naming `eukhe.daemon` and a version. The lowest accepted version equals the daemon's own: the daemon accepts exactly one version; older gets "protocol too old", newer "the client is newer than the daemon".|`crates/eukhe-daemon/src/protocol.rs:20,277-322`|
|client|`eukhe-client` sends the lower of the daemon's and its own version; the CLI refuses a command when the daemon's protocol is below its own.|`crates/eukhe-client/src/daemon_client.rs:578-592`, `crates/eukhe-cli/src/daemon_command.rs:193-201`|
|unknown input|An unknown command type is a typed error; unknown fields are ignored because no wire type denies them (serde's default), stated nowhere.|`crates/eukhe-daemon/src/protocol.rs:273-285`|
|replacement|Only an interactive start replaces a daemon, only an idle one of a lower version; a newer daemon or another build is kept and the user is told. This, not a version range, is how versions meet today.|`bend/replace.bend`, `laws/replace.bend`, `bend/launcher.bend`, `crates/eukhe-client/src/daemon_build.rs`|
|tests across versions|Mock daemons of other versions: an idle older daemon is replaced, a busy one kept, an older client keeps a newer daemon or exits with its message on another schema, a foreign protocol is replaced.|`crates/eukhe-cli/tests/daemon_replacement_e2e.rs:470-660`|
|events|A cursor (generation, sequence); a resume that is not at the end answers `event_replay_not_available`.|`crates/eukhe-daemon/src/protocol.rs:420-447`|
|other surfaces|`--mode rpc` (stdio JSONL, ported from the TS rpc mode); ACP; the dashboard's own bridge protocol 3 with an allow list of daemon commands (a new command runs nowhere until listed).|`crates/eukhe-daemon/src/rpc/mod.rs`, `crates/eukhe-dashboard/src/protocol.rs:15`, `bend/dash_policy.bend`|
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
   API change (W11).
7. The tests use mocks of other versions, not released builds or recorded
   frames (W13).

### oh-my-pi (c28b3e3, paths under `packages/coding-agent/src` unless rooted)

|Behavior|Where|
|---|---|
|RPC mode: JSONL over stdio; a bad line or an unknown command gets an error response and the stream goes on; unknown fields are ignored ("older runtimes ignore unknown fields"); commands are cast, not validated; every command echoes its `id`.|`modes/rpc/rpc-input.ts:57-60`, `modes/rpc/rpc-mode.ts:474,605,1446-1447,1747,2903`, `docs/rpc.md:113-121,228`|
|Versioning: a `ready` frame with `protocolVersion` 1 and `supportedProtocolVersions` [1, 2]; the client opts in to 2 (`negotiate_protocol`); the only difference is framing; no minimum, old clients are never refused; one feature flag in `ready`.|`modes/rpc/rpc-mode.ts:1421-1431,2023-2026`, `modes/rpc/rpc-types.ts:378-383`, `docs/rpc.md:60,77`|
|Commands added later: "older runtimes reject this command", do not fall back.|`docs/rpc.md:424,443,458`|
|Schema: declared once, clients generated for Python, Rust and Go; the server keeps hand-written types tied by a type-level test; the committed output must equal a fresh run.|`modes/rpc/wire/index.ts:2,13-14`, `packages/coding-agent/package.json:529`, `packages/coding-agent/test/rpc-wire/generated.test.ts`, `packages/coding-agent/test/rpc-wire/conformance.types.ts:146-298`|
|Leniency in the schema: open objects, an unknown-event fallback, absent fields read as a default, an unknown frame type is a notification, not an error.|`modes/rpc/wire/index.ts:9,52,105-107`, `modes/rpc/wire/state.ts:108-143`|
|Session file: `version` 3, migrated on load; a newer version than the reader knows is accepted without a warning. A session archive is an exact-version gate.|`session/session-migrations.ts:14-70`, `session/session-transfer.ts:48,366-369`|
|SDK: no stable-versus-internal split and no semver statement; all packages share one version; breaking changes ship in patch releases under "Breaking Changes".|`docs/sdk.md:21,241-242`, `packages/coding-agent/CHANGELOG.md:9-13,83-87`, `AGENTS.md:320-335`|
|Other protocols: exact-match versions (collab, stream, native addon), a hello with features (TSP), MCP's version adopted from the server unchecked. `pi-wire` states "receivers tolerate unknown future fields".|`packages/wire/src/index.ts:389-401`, `packages/wire/src/stream.ts:19-20`, `packages/wire/src/tsp.ts:24,1092-1099`, `mcp/client.ts:100,120`, `packages/wire/README.md:29-31`|
|Extensions: no API version; compatibility by shims for removed symbols and renamed package scopes.|`extensibility/legacy-pi-coding-agent-shim.ts:1651-1654`, `extensibility/plugins/legacy-pi-compat.ts:816`|

omp has no behavior for: a version range or a refusal of a client too old
or too new; validation of commands; a rule for a newer session file; a
semver or deprecation policy; a test of an old client against a new server
or the reverse. Where omp has the behavior this pillar matches it: one
schema with generated clients, unknown fields and unknown frames tolerated,
a feature flag in the first frame, "do not fall back" for a missing
command. The window, the checker and the matrix are designed, not ported.

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
|W9|`format_newer_refused`|A file of a format above the reader's is refused, its bytes are unchanged, and the refusal carries the file's version and the reader's.|omp's silent accept of a newer version.|
|W10|`one_response_per_command`|For every order of commands and events, each command id gets exactly one response.|A timeout and a late reply both sent.|
|W10|`event_seq_gapless`|Per session, what a client receives is events with sequence numbers rising by one, or a marked gap (shared with orchestration O13).|A reconnect that restarts the sequence.|
|W12|`upgrade_answers_or_tells`|For a client of any range attached across a replacement, either negotiation with the new daemon agrees and its next command is answered, or it receives the error of `proto_refusal_exact`.|A connection closed with no reason.|

W12's first clause is already proven: the replacement and idle-shutdown
laws (`laws/replace.bend`, `laws/launcher.bend`) and the resume law of
tasks (D3). W11's second sentence and W13 are process rules: the schema is
generated and committed, the SDKs are generated from it, and the matrix
runs before a release (section 7).

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

## 6. Surface

- Hello: `protocol {name, lo, hi}`, `schema {id, version}`, `capabilities`,
  `deprecations [{feature, since, removal, use}]`. Client: `protocol {lo,
  hi}` in its first envelope. Errors: `protocol_no_common_version`,
  `unknown_command`, `not_supported`, `critical_unknown`.
- CLI: `eukhe daemon protocol` (ranges, capabilities, deprecations in use by
  attached clients), `eukhe schema check <old> <new>`, `eukhe schema print`.
- SDK: `client.protocol()` (the agreed version), `client.supports(feature)`,
  a deprecation callback.

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

## 8. Trust

Proven: negotiation, the checker against its meaning, tolerant decoding,
the history rule, the dispatch and client models. Trusted: that the
committed schema is what the Rust types serialise (a generated file with a
staleness test), JSON parsing, the released binaries used by the matrix.
Not covered by any proof: meaning that no schema states (what a command
does); the matrix tests that.

## 9. Open questions for the user

1. The window: which older clients must a new daemon serve (the previous
   major, every release of the last N months, everything since 1.0)? And
   how long is the deprecation notice?
2. What is "the SDK"? (a) the wire and `eukhe-client` only; (b) generated
   clients for TypeScript and Python too (omp generates Python, Rust and
   Go); (c) also the in-process `eukhe-sdk`, which then needs its own
   narrow API instead of re-exported engine types.
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
   frame (assumed) or coerce, as omp does not validate at all?
8. A session written by a newer build, opened by an older one: refuse
   (assumed) or open read-only?
9. The matrix: keep released binaries for the window (exact, heavy) or
   recorded frames per release (light, assumed for clients) or both?
