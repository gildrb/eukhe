# security (spec): capability security

Status: spec only. Nothing below is implemented; no law named in section 4
exists yet. Ids `C1..C14` are provisional.

What an agent may read, write, run and send is one proven policy. A subagent
never holds more rights than its parent granted. Secrets and private data
leave only through a granted capability. The pillar builds on the path
policy, the approval gate and its route, the child environment, the outbound
scrubber and the copy-on-write child workspace; it replaces none of them, it
gives them one vocabulary and adds what is missing: grants, attenuation,
labels on data, and confinement of the programs an agent runs.

## 1. Words

- **principal**: a user (through an attached client), or an agent (a session:
  a root, or a subagent with exactly one parent).
- **effect**: what an agent causes outside its own context. Four actions:
  **read** (a path, an `ssh://` host, another agent's chat, memory),
  **write** (a path), **run** (a program, a cell, an MCP stdio server, a
  hook), **send** (bytes to a destination: a model provider, a network host,
  an MCP server, another agent).
- **target**: a path at its real location (symlinks followed), a program at
  the file that would run, a destination by its exact host name or agent id.
- **label**: how sensitive data is: `public < private < secret`. Key files
  of other programs (ssh keys, cloud and registry credentials: the path
  policy's secret class) are secret data.
- **credential**: a value eukhe itself authenticates with: what its auth
  store holds and the credential variables of its environment. Not data: it
  has no label and no capability reads it (C8).
- **store**: where the policy lives: the capability sets, the denials, the
  labels of stored data, the policy's configuration, the decision record.
- **capability**: an action, a scope (a path tree, a file, a program, a
  destination) and a ceiling (the highest label of the data it may carry).
  It **covers** an effect of the same action whose target is inside the
  scope and whose data is at most the ceiling. No scope contains the store
  or eukhe's credentials.
- **denial**: a capability a user took away at an agent. It applies to that
  agent and its whole subtree.
- **set**: the capabilities one agent holds. An effect is **allowed** when a
  capability of the agent's set covers it and no denial at the agent or at
  an ancestor covers it.
- **grant**: how a capability entered a set: the user's configuration, a
  user's act through a client (an answer to a question, or a grant), a
  parent at spawn. **origin**: the chain of grants back to a user.
- **grantable**: an effect a user may allow: every effect except a read of a
  credential and an effect that cannot be judged (C12).
- **context label**: the highest label of anything an agent's context holds.

## 2. Requirements

|Id|Requirement|
|---|---|
|C1|Complete mediation. Every effect of every agent is decided before it happens, by one policy, from the agent's set, the denials above it and the effect alone: allow, ask, or refuse. No tool, runner, kernel, MCP server, extension, hook or subagent reaches a file, a program, the network or another agent any other way, and an effect that happens is the one that was decided.|
|C2|Exact cover. The decision allows exactly the allowed effects. A path is judged at its real location and by its segments, a host by its exact name, a program by the file that would run. Anything else is asked or refused; a question names a capability that, once held, allows that same effect.|
|C3|No ambient authority. An agent with an empty set causes no effect. A capability enters a set only by a grant: the user's configuration (a root agent), a user's act through a client, a parent at spawn. Nothing an agent reads or receives adds one: no file, tool result, model output, message, or setting of an untrusted project.|
|C4|Attenuation. At every moment, an effect a subagent is allowed through what its parent granted is an effect its parent is allowed. What a user gave a subagent directly is the only thing it may hold beyond its parent. A spawn that asks for more than the parent is allowed is refused whole and changes nothing.|
|C5|Revocation reaches the subtree. Taking a capability away at an agent stops, for that agent and every descendant, every effect it covers, before the next effect of any of them is decided. It always succeeds; only a user undoes it; effects it does not cover, and agents outside the subtree, are decided as before.|
|C6|Labels follow data. Data read from a secret place is secret; data from a place the user marked private, or holding a value the scrubber finds personal, is at least private. Everything an agent produces carries at least its context label: a tool result, a summary, a memory line, a file it writes, a message, a child's prompt, a report; what is stored reads back with its label. Only C13 lowers a label.|
|C7|No exit without a capability. An agent sends data labelled L to a destination only when it is allowed a send to that destination with a ceiling of at least L, or a user released exactly that send (C10, C13). A remote model provider is a destination like any other: a request to it sends the whole context. Two runs that differ only in their secret data, with none of it released, send the same bytes to every destination not allowed secret data.|
|C8|Credentials are never data. A credential is used only by the host, only on a request to the destination it is bound to. Its value never appears in an agent's context, a child process's environment, a message, the record, or a request to another destination. A read of one is refused, never asked.|
|C9|A program holds no more than its agent. A program an agent runs is confined by the operating system to what the agent is allowed to read, write and send; it reaches a host only when the agent may send that host the most sensitive data the program can read. Where the system cannot confine a run, the run needs the capability `run unconfined`, which no default set holds and which no spawn passes on.|
|C10|Asking. An effect that is not allowed and is grantable asks a user while a client can answer: the question goes up the agent chain to the first session with an attached client. The answer allows exactly the asked effect once, or grants one named capability that covers it for the session. No client, no answer, a denial, or a headless run: refused. Only a user answers: never an agent, a model, or a timeout that says yes; a client that cannot show a question answers only by the rule the user configured for it.|
|C11|The policy protects itself. Nothing an agent does changes the store: no effect of any action, no message, no command it sends to the daemon or through the CLI. A write to the store's files asks a user whatever the set holds.|
|C12|Safe on doubt. A target that cannot be judged (links that loop, a URL that does not parse, an effect of an unknown kind, a program that cannot be identified) is allowed by no capability and is not grantable. A failure of the decision itself refuses.|
|C13|Declassification is explicit. Only a user's answer releases one labelled value to one destination, once. Any other value, destination or time stays refused.|
|C14|Visible. A client can read every agent's set and denials with each capability's origin; every decision reaches the clients once, naming the capability that allowed it or the reason it was asked or refused; a client can grant, take away and answer. Every decision is in the record (`spec/record/SPEC.md` T1).|

## 3. What exists in eukhe

### eukhe (origin/merge/main-into-client-sdk)

|Area|What it decides today|Where|
|---|---|---|
|effects and the auto set|A `bash` step or `ipython` cell has a set of effects (read, write, exec, net, outside, protected, secret); it runs unasked only when all are in `shell.autoEffects`. Default: all seven, so by default nothing asks.|`bend/tools.bend` §4, `bend/runners.bend`, `crates/eukhe-types/src/shell.rs`, `crates/eukhe-core/src/settings/cvar/table.rs:1219`|
|path policy|A path is judged at its real location: Secret, Protected, Inside, Outside; a loop is never Inside; writes with no yes leave every secret as it was. Shell and document tools share it.|`bend/path_policy.bend`, `laws/path_policy/` (64 laws), `crates/eukhe-types/src/path_policy.rs`, `crates/eukhe-core/src/durable/path_policy.rs`|
|approval route|A question goes up the chain of sessions to the first client that answers; above the root it is unanswered, a denial. The phone gateway shows no question: its rule answers at once (a protected write is refused, every other step runs).|`bend/approvals.bend`, `laws/approvals/` (33)|
|runners|Every tool that runs code goes through the gate (`gate_covers_every_runner`); main's roster is read-only tools plus worker tools.|`bend/runners.bend`, `laws/runners.bend`|
|child environment|No credential variable reaches a child process; a local kernel keeps only the names the user's MCP config lists.|`bend/child_env.bend`, `laws/child_env.bend` (`env_drops_credentials`)|
|outbound scrubber|With `privacy.anonymizeRemote`: personal values leave as tokens that map back; credentials leave as one-way tokens; a local model gets the raw text.|`bend/privacy/`, `spec/harness/privacy.bend`, `laws/privacy/` (H7)|
|child workspace|A subagent spawned with `isolate` works on a copy; changes merge back path by path, conflicts reported. A protocol model of host and sandbox frames. No operating-system sandbox: a search for landlock, seatbelt, bwrap, seccomp finds nothing.|`bend/sandbox.bend`, `laws/sandbox.bend`, `crates/eukhe-core/src/child_workspace/`|
|who spawns, who messages|A spawn needs a reason (`parallel`, `isolate`, `tools`, `user`), depth and family cap; an agent messages only its parent and children.|`bend/family.bend`, `bend/kin.bend`|
|project trust|Keys of `<project>/.eukhe/settings.json` that run code, redirect credentials or raise a limit apply only under `trustedProjects`.|`crates/eukhe-core/src/settings/trust.rs`, `laws/config.bend` (`untrusted_changes_nothing_guarded`)|
|local access|Socket dir owned by the user, peer of the same uid, private file modes; dashboard Host/Origin checks and command allow list; MCP catalog refuses loopback and private hosts; `ssh://` reads only to `ssh.hosts`.|`bend/fsmode.bend`, `bend/dash_access.bend`, `bend/dash_policy.bend`, `bend/mcp_url.bend`, `crates/eukhe-core/src/durable/documents/ssh.rs`|

Gaps against the requirements:

1. No capability or grant exists. Rights are spread over settings
   (`shell.autoEffects`, `ssh.hosts`, `mcpServers`, `trustedProjects`) and
   each gate reads its own (C1, C2, C14).
2. No attenuation. A subagent starts from its parent's setting values and
   its own profile (`subagent.cfg`, `agents/<name>.cfg`) and its own sets may
   widen a Local setting such as `shell.autoEffects`
   (`crates/eukhe-core/src/settings/cvar.rs:11-23`). No law relates a child's
   rights to its parent's (C4, C5).
3. The gate judges what a step names. A program the agent runs (effect
   `exec`) then reads and sends what the operating system lets the user do:
   no confinement (C9). `net` is one effect with no destination (C2, C7).
4. No label on data. A secret read under the default auto set enters the
   context and goes to the provider in the next request; the scrubber's
   credential patterns are the only stop, and only when it is on (C6, C7).
5. A yes is one step's; nothing is remembered, nothing is taken away
   (C5, C10).

## 4. Proposed laws (requirement laws only)

Each line: the law, what it states, and one wrong program it rejects. The
entry laws every compiled-core entry carries (`*_entry_is_spec`,
`*_entry_reads`, `*_entry_refuses`) come with the implementation and are
not listed. "Host model" is the Bend model of the host's loop: the events an
adversary orders (effects asked, results, messages, grants, spawns, answers,
crashes) and the actions the host emits.

|Req|Law|States|Rejects|
|---|---|---|---|
|C1|`cap_effect_follows_decision`|In the host model every effect action, whatever asked for it (a tool, a runner, a kernel, an MCP server, an extension, a hook, a subagent), comes right after an allow, or a user's yes, for that same action, target and label.|A tool that declares a read and writes; a hook that runs before the gate.|
|C1|`cap_gate_covers_every_tool`|Every tool of the registry declares the effect kinds it can cause, and each kind is one the decision judges (extends `gate_covers_every_runner` from runners to all tools).|A new tool with no declaration.|
|C2|`cap_allow_iff_allowed`|The decision is allow exactly when a capability of the set covers the effect and no denial at the agent or an ancestor covers it.|A write allowed by a read capability; a ceiling ignored; a first-match list where one entry shadows another.|
|C2|`cap_cover_by_segments`|A path is inside a tree scope by its segments, on its real path.|`/work2` taken as inside `/work`; a link inside the scope that points out.|
|C2|`cap_host_exact`|A host scope covers a destination only of the same name (ASCII case aside).|`evil-github.com` matching `github.com` by suffix.|
|C2|`cap_program_resolved`|A program scope covers a run only when the file that would run, after the search path and links, is the scope's file.|A `./git` earlier on the path run under a capability for `/usr/bin/git`.|
|C2|`cap_ask_names_missing`|The capability a question names, added to the set, allows that same effect; a refusal of an effect that is not grantable names none.|A hint that names the wrong path or action.|
|C3|`cap_only_grants_change_sets`|Over any run of the host model (effects, results, messages, settings loads, grants, spawns, answers), a set gains a capability only at a load of the user's configuration, a user's act through a client, or a spawn.|A tool result or a message parsed as a grant.|
|C3|`cap_untrusted_project_grants_nothing`|A root's first set is the same with and without the settings of an untrusted project.|A project file with a `capabilities` key read as the user's.|
|C4|`cap_child_within_parent`|In every reachable state, an effect a child is allowed by a capability it got at spawn is allowed to its parent.|A child profile that widens the auto set; a grant checked against the root instead of the parent; a denial at the parent that the child escapes.|
|C4|`cap_spawn_all_or_none`|A spawn asking one capability whose effects the parent is not allowed is refused and the state is unchanged.|A spawn that silently drops the capability, or grants it.|
|C4|`cap_origin_reaches_user`|Every capability of every reachable set has a chain of grants that ends at a user's configuration or act, each link allowed to its granter when it was made.|A capability an agent mints for itself or for a sibling.|
|C5|`cap_revoke_reaches_subtree`|After a capability is taken away at an agent, no agent of its subtree is allowed an effect it covers.|A revoke that updates the agent and forgets its grandchildren.|
|C5|`cap_revoke_spares_others`|After it, every effect it does not cover, and every effect of an agent outside the subtree, is decided as before.|A revoke that clears whole sets.|
|C5|`cap_revoke_total`|Taking away succeeds in every state, and over any later run of the host model only a user's act removes the denial.|A revoke refused while a descendant runs; a respawn that drops the denial.|
|C6|`label_never_drops`|Over any run of the host model, a context label falls only at a user's release.|A compaction or a summary that resets the label.|
|C6|`label_follows_output`|A tool result, summary, message, child prompt or report carries at least its maker's context label, and a receiver's context label is at least that after delivery.|A report from a child that read a secret arriving public.|
|C6|`label_stored_reads_back`|A file or memory line written under a context label reads back with at least that label.|A secret copied into the workspace and read again as public.|
|C6|`label_sources`|A read whose real path the path policy classes Secret yields secret data; a read from a place the user marked private, or of a text holding a value the scrubber classes personal, yields at least private data.|A read through a symlink that arrives public.|
|C7|`send_allow_iff_ceiling`|The decision allows a send exactly when the agent is allowed a send to that destination with a ceiling at least its context label.|Any send allowed once `net` is granted.|
|C7|`send_noninterference`|Two runs of the host model equal in everything but secret data, with no release, produce equal sends to every destination not allowed secret data.|A refusal text that quotes the secret; a scrubber path skipped on failover.|
|C7|`provider_is_destination`|A request to a remote model is a send to its host; a request to a local model is no send.|The provider exempt from the policy.|
|C8|`cred_read_refused`|A read of a credential is refused for every set, and never asked.|A yes that opens `auth.json` once.|
|C8|`cred_absent_everywhere`|No credential value occurs in any context entry, message, child environment or record entry the host model produces, for every value of the credential registry (the exact values, not patterns).|A tool output that prints a key and is stored raw.|
|C8|`cred_bound_to_destination`|The host attaches a credential only to a request whose destination is the one the credential is bound to.|A project `baseUrl` that receives another provider's key.|
|C9|`profile_within_allowed`|The confinement profile built for an agent permits a path only when the agent is allowed that read or write, and a host only when the agent is allowed to send it the highest label among the paths the profile lets the program read.|A profile that opens the home directory for convenience; a public host open to a program that reads secret paths.|
|C9|`run_unconfined_needed`|When the host reports that a run cannot be confined, the run is allowed only by `run unconfined`.|An unsupported system that runs the program anyway.|
|C9|`run_unconfined_not_default_not_passed`|No default set holds `run unconfined`, and no spawn grants it.|A child inheriting the parent's unconfined shell.|
|C10|`ask_when_grantable`|An effect that is not allowed and is grantable yields a question, not a refusal, while some session up the chain has a client.|A policy that refuses everything it does not allow.|
|C10|`ask_grants_exactly_asked`|After the answer "once" the set is unchanged and exactly the asked effect runs; after "session" the set gains exactly the one capability the question showed, which covers the asked effect.|A yes that widens to the whole directory tree.|
|C10|`ask_only_user_answers`|An answer counts only from a client that showed the question, or as the rule the user configured for a client that cannot show one; any other answer changes nothing and the effect does not run.|A parent agent approving its child; a built-in yes for the gateway.|
|C11|`policy_untouched_by_agents`|Over any run of the host model, no event an agent authors (an effect of any action, a message, a command to the daemon) changes a set, a denial, a stored label, the configuration or the decision record.|An agent that runs the grant command of the CLI, or sends the grant command over the socket.|
|C11|`policy_write_always_asks`|A write whose real path is one of the store's files asks, for every set.|A broad write capability over the home directory editing the policy.|
|C12|`cap_doubt_is_restricted`|A path that loops, a destination that does not parse, an unknown effect kind and a program that cannot be identified are allowed by no set and are not grantable.|An unparsed URL treated as public.|
|C12|`cap_failure_refuses`|When the decision cannot be computed (a malformed request, an entry error), the host model's verdict is a refusal.|A fallback to allow when the rule fails.|
|C13|`declassify_exact`|A user's release of one value to one destination allows exactly that send once.|A release that unlabels the whole context.|
|C14|`caps_view_exact`|What a client reads for an agent (capabilities with origins, denials) equals what the agent holds.|A view that omits what a user's answer granted.|
|C14|`decision_event_once`|Each decision emits exactly one event, naming the capability that allowed it or the reason it was asked or refused.|A refusal no client ever sees.|

`cap_allow_iff_allowed` at the empty set is C3's first sentence: nothing
covers, so nothing is allowed.

Already proven and reused as they stand: `path_real_*`, `path_judge_*`,
`store_refused_write_keeps` (real paths and classes); the approvals route
(`child_answered_by_root`, `unanswered_only_when_quiet`); `gate_yes_runs`;
`env_drops_credentials`; the privacy token laws (a credential leaves one
way); `untrusted_changes_nothing_guarded`.

## 5. Core sketch

`bend/cap.bend` (plain calls) and `bend/cap_tree.bend` (a stepper; its state
is a durable document so sets survive a restart):

```
type Action:  Read | Write | Run | Send
type Label:   Public | Private | Secret
type Scope:   Tree{path} | File{path} | Prog{path} | Host{name} | Agent{id}
type Cap:     Cap{act, scope, ceil}
type Effect:  Effect{act, target, label}
type Verdict: Allow{by} | Ask{need: Cap} | Refuse{why}

decide(chain, effect) -> Verdict                  # chain: the agent's set and the denials up to the root
spawn(parent_chain, asked) -> Maybe<Set>          # C4, all or none
step(tree, event) -> (tree, verdicts)             # Config Grant Answer Spawn End Revoke Effect Deliver Release
join(a, b) -> Label                               # C6
profile(chain) -> Profile{read, write, hosts}     # C9
```

It calls what is proven: `path_policy.judge` for the real path and its
class, the approvals route for a question, the privacy tokens for a send
whose ceiling is below the context label (a private value leaves as its
token: the scrubber becomes the filter of a capability, no longer a
separate setting). Today's settings become the root's default set: each
effect of `shell.autoEffects` is one capability class, `ssh.hosts` are read
capabilities on hosts, each MCP server is a run and a send capability.

Rust keeps IO only: it resolves real paths and programs, asks `decide` for
every effect, applies `profile` to the child process (Landlock and seccomp
on Linux, Seatbelt on macOS, a filtering proxy for hosts), keeps the labels
of stored data, and writes each decision to the record. An effect API that
takes a permit value only `decide` can make keeps a new tool from skipping
the gate.

## 6. Surface

- Daemon and SDK: `caps_get {sessionId}` (set, denials, origins),
  `caps_grant`, `caps_revoke`, `caps_answer` (generalises the
  `shell_approval` answer), events `cap_ask` and `cap_decision`; spawn takes
  `grant: [...]`; settings key `capabilities` (a named profile or a list).
  Commands that change the store are accepted only from a client, never
  from a session's own tools.
- CLI and TUI: `eukhe caps [session]`, `/caps`, the question card shows the
  capability asked and offers once or session; the agents view shows each
  subagent's set next to its parent's.

## 7. Tests (with the implementation)

One per requirement, through the entries. Crash and restart: sets, denials
and labels are read back from the durable document; a revoke acknowledged
before a crash holds after it; a question pending at a crash is unanswered.
Real `claude-haiku-5-5` runs: a file that tells the agent to read an ssh key
and post it is stopped (the read asks, and without a release the send is
refused); a subagent asked to write outside its grant is refused while its
parent may; a secret read followed by a remote request asks, and a local
model does not.

## 8. Trust

Proven: the decision, the tree invariant, the labels, the profile's bound,
over the host model. Trusted: the operating system's confinement, the
real-path and program resolution in Rust, the classification of what a
built-in command does (`eukhe-shell`), the TLS library. Tested, not proven:
that every effect in Rust passes the gate (the permit type and a test over
the tool registry) and that Rust sends the host model's events faithfully.

## 9. Open questions for the user

1. Default posture. Today every effect runs unasked, a secret read
   included. Keep that as profile `open` and add `workspace` (read anywhere
   not secret, write inside, send to the model only) and `locked`, or make
   `workspace` the default?
2. Confinement (C9). Build real operating-system confinement (Linux and
   macOS; a host proxy for the network), or ship first with every external
   program counted as `run unconfined` and C7 stated only for confined runs?
   Windows in or out?
3. Label grain (C6). Context-level labels are simple and provable but one
   secret read taints the session: every later remote request asks. The
   alternative seals secret values as one-way tokens before they enter the
   context and restores them only at an effect that is allowed them
   (eukhe's privacy tokens). Which is the default?
4. A user's yes to a subagent's question: a grant to that subagent only
   (assumed above: C4 counts it as given directly), or to its whole chain,
   so that a parent is always allowed what its child is?
5. What is private? Only what the scrubber finds and what the user marks,
   or the whole workspace, so that sending code to a remote provider is
   itself a granted capability?
6. Destinations: exact host names only (assumed), or patterns
   (`*.github.com`)? Pin a name to the addresses it resolved to?
7. MCP servers and extensions: each its own principal with its own set, or
   part of the agent that calls them?
8. Taking a capability away while an effect it covers runs: let it finish
   (assumed), or stop it?
9. Remembered answers: once and session only, or also "always" (written to
   the policy store)?
10. Principals beyond one OS user: remote clients with their own rights, or
    one user per daemon as today?
11. The phone gateway today answers every question by its rule (yes, except
    a protected write). Under C10 is that a rule the user sets for gateway
    sessions (assumed), or should the gateway ask on the phone?
12. Other programs' key files (ssh, cloud): secret data an agent may be
    allowed to read and use (assumed), or credentials no agent ever reads?
