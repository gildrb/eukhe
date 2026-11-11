# Planned pillars: security, record, orchestration, contract

Status: specs only. `spec/README.md` lists what is proven; this file lists
four pillars that are specified and not built. Each spec is written without
the code: numbered requirements, a map of what eukhe and oh-my-pi (c28b3e3)
do today, the laws proposed (requirement laws only: each names a wrong
program it rejects), a sketch of the Bend core and of the daemon, SDK, CLI
and TUI surface, and the questions the user must decide.

|Pillar|Spec|Ids|One line|Builds on (proven today)|
|---|---|---|---|---|
|capability security|`security/SPEC.md`|C1..C14|What an agent may read, write, run and send is one policy; a subagent holds no more than its parent granted; secrets and private data leave only through a granted capability.|path_policy, approvals, runners, child_env, privacy, sandbox, config trust|
|complete replayable record|`record/SPEC.md`|T1..T12|Every decision and effect is attributed, the record shows tampering, a session replays to the same decisions, one query audits a tree.|log, tree, tool_call, call_lift, arg_repair|
|orchestration at scale|`orchestration/SPEC.md`|O1..O14|Many agents, loops and workflows: fair turns, no deadlock, no lost or duplicated message, bounded queues, admission limits.|admission, family, workflow, rlm_query, kin, child, wait, wait_any, job, task_life|
|stable SDK contract|`contract/SPEC.md`|W1..W13|The wire and the SDKs keep working across upgrades: negotiated versions, unknown fields tolerated, old and new on both sides, rules for removal.|replace, launcher, semver, wire, call_lift|

The id letters are provisional: the pillars built in parallel (budgets,
verified completion, exactly-once, loop) choose theirs, and the table of
`spec/README.md` settles them when a pillar lands.

## Order to build

1. **contract** first. It is the smallest (two plain-call cores, a
   generated schema, a checker in CI) and every other pillar adds commands
   and events: with the rules in place first, each addition is checked
   against the last release instead of being repaired later.
2. **record** second. The other two pillars each produce decisions that
   must be attributed and replayable (a capability decision, an admission),
   their tests use the replay as the oracle, and orchestration fills a slow
   reader's gap from the record.
3. **security** third. It is the largest risk once agents run unwatched,
   and it splits into three steps that can land one by one: the policy
   core with attenuation and revocation (C1 to C5, C10 to C12, C14), labels
   and sends (C6 to C8, C13), confinement of programs (C9), which is the
   long one.
4. **orchestration** last. Its interfaces depend on pillars still in work
   (a budget refuses before a limit; a loop iteration is a unit; delivery
   once is shared with exactly-once), on the record (gaps), and on security
   (limits per principal).

Security and orchestration touch separate files (`bend/cap*.bend` against
`bend/sched.bend`, `bend/mailbox.bend`, `bend/waitfor.bend`,
`bend/stream.bend`) and can be built by two agents at once after the
record.

## Interfaces between pillars

|Between|Interface|
|---|---|
|security, record|Every capability decision is a decision entry (T1) naming the capability used and its origin (C14); the record and its anchors are in the protected class (C11, T11); the record holds no credential (C8, T10).|
|security, orchestration|A limit may be set per principal; a message between agents is a send (C7) and carries its sender's label (C6); stopping a subtree (O11) and revoking in a subtree (C5) reach the same set of agents.|
|record, orchestration|A gap in a client's event stream is filled from the record (O13); scheduler decisions are entries; after a restart the scheduler is rebuilt from durable facts (O14).|
|contract, all|Every new command, event, error code and durable format of the other pillars enters the schema as an addition (W5); a feature whose loss would be unsafe is critical (W7): a capability answer, a revoke, a limit.|
|orchestration, exactly-once|One message id and one rule for "delivered once" (O7, O8).|
|orchestration, budgets|A budget refuses before a limit; one law fixes the order of refusals (as `family_refusal_precedence` does).|
|orchestration, loop|A loop iteration is a unit; a loop's wait is a wait-for edge (O9, O10).|
|record, verified completion|The evidence of a verdict is an input entry; the verdict is a decision entry.|

## How these specs were made

- eukhe: read at `origin/merge/main-into-client-sdk` (0355548): `bend/`,
  `laws/`, `spec/`, `crates/`.
- oh-my-pi: read at c28b3e3; every behavior cited as `path:line`; where a
  line was not verified the spec says less, not more.
- No law, proof, Bend code or Rust code is in this change. The law names
  are proposals: none exists in `laws/`.
- The requirement and law lists were read once on paper by two fresh
  reviewers (a law no wrong program fails, a law that cannot hold, a
  requirement no law states, two requirements that disagree); what they
  found is folded in. That is not the review of laws: before any of these
  laws is called done, the Bend skill's steps apply to the written laws:
  mutation of the core, a blind adversary, and the blind triviality review.
