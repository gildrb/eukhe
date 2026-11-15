# Pillars map

Each pillar of `PHILOSOPHY.md`, traced to the ledger statements behind it (ledger v22), the Eukhe requirement rows those statements cite, the laws that state each row, and the code that runs the proven model, with the status of each. Eukhe read at `origin/main` 878bba3, `design/agent-tree` 36a718e, `design/confinement` 65e5756. The agent tree's rows T1-T14 appear as AT1-AT14 (the record spec owns T1-T12). Status of a row: law (stated by laws in `laws/`, proven in `PROOF.bend`), test (Rust, gated by a test), planned (spec only), design (owner-approved design, nothing built). Spec rows `srNN` are requirements the philosophy moved out and Eukhe has not written yet (`spec-rows.md`).

## Summary

|Pillar|Ledger|Rows|law|law on branch|test|planned|design|
|---|---|---|---|---|---|---|---|
|Scope, confinement and isolation|tm1, ds10|19|3|0|0|3|13|
|Limits|tm2, ds1, ds2|11|11|0|0|0|0|
|Sound report and label|tm3, ds4|2|0|0|1|1|0|
|Checks|tm4, ds3|14|8|0|3|3|0|
|Liveness and attention|tm5, tm6, ds7|32|4|13|0|15|0|
|Authority and stops|tm7, ds6|15|4|0|0|10|1|
|Irreversible effects|tm8, ds8|0|0|0|0|0|0|
|Record, once and loops|tm9, tm10, ds5|40|26|0|1|13|0|
|Trees, data marks and the core|tm11, ds9, ds11|34|8|0|0|26|0|
|The bet|tm12, ds13, bet|0|0|0|0|0|0|

## Scope, confinement and isolation

Text: Guarantees and what Eukhe does: Scope. Ledger: tm1, ds10.

- ds10 status: planned (design settled by the owner: C9, C11, C15-C25, to build with a red team; no sandbox yet: programs run with the user's permissions, labelled 'checks passed, unconfined': V4, V10; protected check files built: V5)
- Spec rows to write: sr18, sr41, sr91, sr96, sr98, sr119, sr136, sr161, sr179, sr200, sr201, sr206, sr207, sr210, sr211

|Row|Requirement|Laws|Code|Status|
|---|---|---|---|---|
|C9|A program holds its grants. Every program run is started under a listed mechanism with the profile the core computed from the run's grants: …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C11|The policy and the state protect themselves. While isolation holds, nothing an agent does and nothing a program it runs does changes the …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C15|Isolation is a fact per position. Every program run shares the user's OS identity; it breaks isolation only when it is not confined, or …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C16|Platforms without a mechanism. A platform that cannot enforce the profile reports so before the run; its program runs need `Unconfined`. …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C17|Report facts (sr18). The record entry of each program run names its outcome, mechanism and version, profile digest, mark, whether it held …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C18|Label. The label carries "unconfined" exactly when some program run of the run (check and proof runs and in-process host tool calls that …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C19|Escape list and disclosures. Each release ships an escape list: per mechanism, its escape classes, each with the date it was listed, and …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C20|Checks are confined to their copy. A check's command and a law check's proof run start under a profile that writes only inside the check's …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C21|Long-lived programs. A kernel, MCP server, language server or file-tool run (§1) keeps the profile it started with and holds no cache grant …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C22|Network through the core. Every connection a confined program opens through the proxy is an effect submitted to the core: a send to the …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C23|In-process placement. Every host tool or callback of the in-process placement declares whether it executes agent-supplied content; a call …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C24|Non-interactive runs. Scheduled, loop and autoresearch runs write only to a harness-owned copy of the scope, which holds no state part (§4, …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C25|Measured. Per listed mechanism and release, Eukhe publishes, with method, sample and date: the escape rate red-teaming finds with the …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|T4|Tamper-evident. Each entry is bound by a hash to all entries before it. Short of a collision of that hash, a record that differs in any …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T8|The whole tree. A child's head is anchored in its parent's record at spawn and at each report, and a root's head in the daemon's ledger at …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T11|Out of an agent's reach. A write or a delete by an agent that targets a record, an anchor or the ledger is refused, whatever the agent …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|V4|The result carries one label: `failed` exactly when a check is refuted on the final state; else, when there is a check and every check is …|9 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|
|V5|The worker has no say in its verdict. It can claim the task done (a final answer; `goal.complete()` under an active goal) and read its …|7 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|
|V10|Honest exit: a headless run (`-p`, `--mode json`) whose task has acceptance checks exits 0 only when every check is confirmed on the final …|3 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|

## Limits

Text: Limits. Ledger: tm2, ds1, ds2.

- ds1 status: partial (worst-case reservation, carving and final-answer reserve built: B1-B11; account ledger, check reserves, declared tool worst case and harness report missing)
- ds2 status: partial (B1: a dimension without a limit is unlimited, as the shipped default now is; recording and showing that source, sr24, not verified)
- Spec rows to write: sr192, sr07, sr08, sr09, sr10, sr11, sr38, sr39, sr40, sr44, sr53, sr56, sr76, sr90, sr94, sr131, sr147, sr148, sr178, sr183, sr184, sr24, sr42, sr46, sr51, sr59, sr60, sr73, sr100, sr113, sr120, sr124, sr132, sr133, sr153, sr160, sr209, sr176, sr177, sr197, sr198

|Row|Requirement|Laws|Code|Status|
|---|---|---|---|---|
|B1|A budget is never exceeded. A task tree's budget limits money, tokens, tool calls and model requests, which are spent, and wall-clock time, …|4 (`laws/budget.bend`)|`bend/budget.bend`, `bend/ffi_budget.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|
|B2|A request that could exceed the remainder is sent with a reduced cap, or not at all: the caller offers its asks in order (the wanted output …|6 (`laws/budget.bend`, `laws/budget_share.bend`)|`bend/budget.bend`, `bend/budget_share.bend`, `bend/ffi_budget.bend`, `bend/ffi_budget_share.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|
|B3|After a request or a tool call returns, its actual spend replaces its reservation: exactly the actual spend is charged, what was reserved …|5 (`laws/budget.bend`)|`bend/budget.bend`, `bend/ffi_budget.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|
|B4|A parent's budget bounds everything spent beneath it. A child without a budget of its own draws from its parent's account: every such agent …|9 (`laws/budget.bend`)|`bend/budget.bend`, `bend/ffi_budget.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|
|B5|A budget survives a crash: no spend is doubled, none is lost. A reservation is on disk before its request is sent and a settlement after it …|5 (`laws/budget.bend`)|`bend/budget.bend`, `bend/ffi_budget.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|
|B6|At exhaustion the agent can still answer. Each agent has its own phase. Work is granted only when it leaves the worst case of the agent's …|9 (`laws/budget.bend`)|`bend/budget.bend`, `bend/ffi_budget.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|
|B7|The agent is told in time, by what it actually spends: a grant says when two steps, each the larger of the agent's largest recent step as …|3 (`laws/budget.bend`)|`bend/budget.bend`, `bend/ffi_budget.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|
|B8|The agent sees its remaining budget and can plan with it: what is free, held, spent and lent in each dimension and the time left are the …|2 (`laws/budget.bend`)|`bend/budget.bend`, `bend/ffi_budget.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|
|B9|The accounting is exact and can be audited: in every spent dimension free, held, spent and lent add up to the budget plus the overrun after …|11 (`laws/budget.bend`)|`bend/budget.bend`, `bend/ffi_budget.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|
|B10|Time is a wall-clock deadline for the whole task tree, set when the budget is set and kept across restarts. Every reservation ends by the …|5 (`laws/budget.bend`)|`bend/budget.bend`, `bend/ffi_budget.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|
|B11|A child never takes the reserve of an agent above it: every reservation of an agent drawing from a shared account (work or its own final …|4 (`laws/budget.bend`)|`bend/budget.bend`, `bend/ffi_budget.bend`, `crates/eukhe-bend/src/rules/budget.rs`|law|

## Sound report and label

Text: Sound report. Ledger: tm3, ds4.

- ds4 status: partial (verdicts and totals reported; size bound, witnessed/asserted split and counts equal to the record missing)
- Spec rows to write: sr194, sr03, sr18, sr78, sr81, sr91, sr93, sr109, sr119, sr134, sr146, sr189, sr163, sr193

|Row|Requirement|Laws|Code|Status|
|---|---|---|---|---|
|V8|The verdict, the checks and the evidence are durable and visible to every client: each verdict is committed to the session with what the …|tests `the_verdict_its_checks_and_evidence_are_recorded_and_watched`, `a_later_effect_of_the_worker_makes_the_result_unv|-|test|
|T9|Audit. One query over a tree answers: for an effect (a write to a path, a program run, a send to a host), which agent did it, by which …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|

## Checks

Text: Checks. Ledger: tm4, ds3.

- ds3 status: partial (owner-set checks and labels built: V1-V12; disposable copy, qualifiers, held-out checks, closure, measured rates missing)
- Spec rows to write: sr63, sr191, sr206, sr12, sr13, sr28, sr32, sr43, sr48, sr56, sr75, sr87, sr96, sr135, sr145, sr152, sr167, sr174, sr175, sr182, sr186

|Row|Requirement|Laws|Code|Status|
|---|---|---|---|---|
|V1|A task may carry acceptance checks: a command with the exit code it must end with (and the files the worker must not change), a condition …|3 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|
|V2|A check is judged from what the harness itself observed. A command check is confirmed exactly when its protected files are intact and the …|6 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|
|V3|"Done" is a claim: the harness reports it as success only when every check is confirmed on the final state. The state is a number that …|18 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|
|V4|The result carries one label: `failed` exactly when a check is refuted on the final state; else, when there is a check and every check is …|9 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|
|V5|The worker has no say in its verdict. It can claim the task done (a final answer; `goal.complete()` under an active goal) and read its …|7 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|
|V6|The judge is independent and sees evidence, not the worker's account: it is one model request of its own, with no tools and no transcript, …|tests `a_judge_reads_the_evidence_and_never_the_workers_words`, `the_intent_judge_reads_the_users_messages_and_never_the|-|test|
|V7|A failed check returns its evidence to the worker or ends the task, never as success: the verifier runs every check that did not judge the …|8 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|
|V9|A crash or restart never turns an unverified result into success: a verdict comes only from the verifier's record (a step of the verifier …|3 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|
|V10|Honest exit: a headless run (`-p`, `--mode json`) whose task has acceptance checks exits 0 only when every check is confirmed on the final …|3 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|law|
|V11|The goal is what the conversation currently asks for: a later user message that adds a requirement extends the task, one that drops a …|tests `a_requirement_added_later_extends_the_task`, `a_side_question_neither_ends_nor_fails_the_task`, `the_intent_judge|-|test|
|V12|A parent may give its child's task acceptance checks: the parent is the owner of that task (V1), it sets the checks at the spawn, and the …|test `a_parent_sets_its_childs_checks_and_reads_its_verdict` (`crates/eukhe-core/src/durable/children/tests.rs`)|-|test|
|V13|Planned (next branch, not built): held-out checks. The owner may set acceptance checks the worker never sees: not in its context, not …|planned: laws on the label with held-out slots; test that no worker read shows a held-out check|-|planned|
|V14|Planned (next branch, not built): faithfulness review. "Done" reached unfaithfully is not done: an independent judge (a model request that …|planned: laws on the review's place in the label and the return; tests with scripted gaming sessions; real runs|-|planned|
|V15|Planned (next branch, not built): the label verifies the process, not only the outcome. `verified` exactly when every outcome check is …|1 (`laws/verify.bend`)|`bend/ffi_verify.bend`, `bend/verify.bend`, `crates/eukhe-bend/src/rules/verify.rs`|planned|

## Liveness and attention

Text: Liveness; Attention; agent tree. Ledger: tm5, tm6, ds7.

- ds7 status: partial (questions to the first client, headless denial built; the phone gateway answers yes to unprotected steps, against tm6; bounds, commitment bound, park causes, notices and orchestration rules missing; the agent tree is specified with laws, AT1-AT14, and no Rust runs it yet)
- Spec rows to write: sr205, sr04, sr05, sr06, sr20, sr34, sr35, sr36, sr55, sr68, sr71, sr74, sr95, sr99, sr101, sr140, sr149, sr151, sr168, sr202

|Row|Requirement|Laws|Code|Status|
|---|---|---|---|---|
|C10|Asking. An effect that is not allowed and is grantable asks a user while a client can answer: the question goes up the agent chain to the …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|D4|Every run ends; every wait has an exit: a headless run (`-p`, `--mode json`, `--mode rpc`) stops waiting only when nothing runs, nothing is …|8 (`laws/headless_settle.bend`, `laws/run/model.bend`)|`bend/ffi_headless_settle.bend`, `bend/ffi_run.bend`, `bend/headless_settle.bend`|law|
|OR1|Admission. A unit starts only when every limit on its path has room: the daemon's, its tree's, its provider's. A unit, or a batch as a …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR2|Slots are conserved. The units that count under a limit never exceed it. A unit that ends, is stopped, or whose process dies stops counting …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR3|Every queue is bounded. Each queue has a declared bound it never passes and a declared mode at the bound. Below the bound an offer that …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR4|No starvation between trees. An eligible unit is passed by at most a bounded number of admissions of its own class from other trees (one …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR5|Interactive first, background still served. While an interactive unit is eligible, a background unit is admitted ahead of it only when it …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR6|Work-conserving. After every step no waiting unit is eligible: room and a unit that could use it never both remain.|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR7|No lost message. An accepted message is delivered to its target exactly once, or returned to its sender with the true reason (the target …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR8|No duplicate, in order. A message redelivered after a crash or a retry is recognised by its id: the target sees each id once. Messages from …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR9|No deadlock. The wait-for relation among agents, loops, workflows and tasks never holds a cycle: a wait that would close one is refused …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR10|Every wait has an exit. A wait is accepted only when something it watches still runs or it has a deadline; a wait on nothing is refused at …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR12|Control is never queued. A status request is answered in the step it arrives, with the true state; a stop takes effect; neither takes a …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR13|A slow reader hurts only itself. What a client receives depends only on the events and on its own reading: a client that reads slowly never …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR14|Survives restart, and is visible. After a daemon restart the scheduler's state is rebuilt from durable state: no unit lost, none admitted …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|R3|`rlm.query`/`query_batch` (tool-less sub-model calls whose results return as values): budget first, then the concurrency cap, then waves …|7 (`laws/rlm_query.bend`)|`bend/ffi_rlm_query.bend`, `bend/rlm_query.bend`, `crates/eukhe-bend/src/rules/rlm_query.rs`|law|
|M2|A compactor line fits its budget; interactive requests never wait behind background work.|compactor laws, admission laws|-|law|
|A3|An agent messages only its parent and its own children, never itself or across trees; an admitted message always reaches the target's …|7 (`laws/kin.bend`)|`bend/ffi_kin.bend`, `bend/kin.bend`, `crates/eukhe-bend/src/rules/kin.rs`|law|
|AT1|A node splits only from a running leaf into exactly two children, admitted exactly when own, left and right split its scope unit by unit, …|3 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT2|In every tree reachable from a root by any events (a run applies the events one by one, a refused one keeping the tree), the own scopes of …|3 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT3|Integrating a child's patch applies exactly its writes inside the child's scope, over the parent's patch; every write outside is reported …|6 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT4|For two children with disjoint scopes, integrating left then right gives the same files as right then left.|1 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT5|For a tree whose every patch stays in its node's scope and whose splits split their scopes, the files with the root's integrated patch …|1 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT6|A node finishes only while running, a split only once both children settled; in every reachable tree no running node sits under a settled …|3 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT7|After a cancel or a fail of a node no node of its subtree runs and nothing outside it changes; a cancel marks each running node of the …|8 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT8|A spend is admitted exactly when its node runs and the amount fits its room (limit - own spend - each child's hold: a running child's …|9 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT9|Every reachable tree has depth <= `max_depth` and, with `max_nodes` >= 1, at most `max_nodes` nodes; a split the configured bounds allow is …|6 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT10|A node's next action is to wait exactly when no user message, no arrived child result and no own work is there; a user message comes first, …|4 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT11|A redo restarts a failed or cancelled leaf under a running parent as a running leaf with its scope, spend, deadline and partial patch, its …|1 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT12|Planned (not built): the TUI shows the tree live, one row per node: status, scope, elapsed, cost. Rust, so the gate is a test.|planned: test of the TUI tree view (branch `design/agent-tree`)|-|planned|
|AT13|The compiled core answers every request Rust spells with the model's decision, and refuses every other input with one error.|5 (`laws/agent_tree.bend (branch)`)|`bend/agent_tree.bend`, `bend/ffi_agent_tree.bend`|law (branch; no Rust runs it)|
|AT14|Writers form the binary tree; a running node may ask a read-only helper (help): an extra leaf with no write scope (integrating its patch …|15 (`laws/agent_crown.bend (branch)`)|`bend/agent_crown.bend`|law (branch; no Rust runs it)|

## Authority and stops

Text: Authority. Ledger: tm7, ds6.

- ds6 status: partial (approval gate, path classes, spawn admission, credential-free children built; one policy, empty default, revocation, subtree stop and teardown planned)
- Spec rows to write: sr10, sr40, sr47, sr164, sr172

|Row|Requirement|Laws|Code|Status|
|---|---|---|---|---|
|C1|Complete mediation. Every effect of every agent is decided before it happens, by one policy, from the agent's set, the denials above it and …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|C2|Exact cover. The decision allows exactly the allowed effects. A path is judged at its real location and by its segments, a host by its …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|C3|No ambient authority. An agent with an empty set causes no effect. A capability enters a set only by a grant: the user's configuration (a …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|C4|Attenuation. At every moment, an effect a subagent is allowed through what its parent granted is an effect its parent is allowed. What a …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|C5|Revocation reaches the subtree. Taking a capability away at an agent stops, for that agent and every descendant, every effect it covers, …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|C8|Credentials are never data. A credential is used only by the host, only on a request to the destination it is bound to. Its value never …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|C11|The policy and the state protect themselves. While isolation holds, nothing an agent does and nothing a program it runs does changes the …|none yet (design; law names proposed in `spec/security/CONFINEMENT.md` §6 on branch `design/confinement`)|-|design|
|C12|Safe on doubt. A target that cannot be judged (links that loop, a URL that does not parse, an effect of an unknown kind, a program that …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|C14|Visible. A client can read every agent's set and denials with each capability's origin; every decision reaches the clients once, naming the …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|R1|A subagent is admitted only with a reason (`parallel`, `isolate`, `tools`, `user`), below the depth limit, inside the family cap; a batch …|7 (`laws/family.bend`)|`bend/family.bend`, `bend/ffi_family.bend`, `crates/eukhe-bend/src/rules/family.rs`|law|
|A2|Every runner goes through the approval gate.|1 (`laws/runners.bend`)|`bend/ffi_runners.bend`, `bend/runners.bend`, `crates/eukhe-bend/src/rules/runners.rs`|law|
|OR11|Stopping scales. Stopping an agent ends exactly the units of its subtree, within a bound that grows with the subtree's size. Outside the …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|OR12|Control is never queued. A status request is answered in the step it arrives, with the true state; a stop takes effect; neither takes a …|planned (spec only; proposed laws in `spec/orchestration/SPEC.md`)|-|planned|
|L5|A loop is always stoppable. After the user's interrupt (Esc, an abort) no turn and no check starts until the user sends a prompt or …|3 (`laws/loop/history.bend`, `laws/loop/model.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|O4|A started effect with no end on record, about which the world says nothing, is reported interrupted at the restart: never launched again, …|3 (`laws/once.bend`)|`bend/ffi_once.bend`, `bend/once.bend`, `crates/eukhe-bend/src/rules/once.rs`|law|

## Irreversible effects

Text: Irreversible effects. Ledger: tm8, ds8.

- ds8 status: gap (no requirement; only a copy-on-write workspace exists)
- Spec rows to write: sr195, sr10, sr29, sr40, sr45, sr54, sr112, sr113, sr139, sr170, sr171, sr208

## Record, once and loops

Text: Record and once. Ledger: tm9, tm10, ds5.

- ds5 status: partial (intent journal and at-most-once built: O1-O9; O7 resends a keyed effect up to a cap without a declared deduplication contract, against va6; record T1-T12 planned)
- Spec rows to write: sr01, sr02, sr15, sr16, sr17, sr21, sr33, sr53, sr57, sr67, sr76, sr79, sr89, sr97, sr102, sr108, sr165

|Row|Requirement|Laws|Code|Status|
|---|---|---|---|---|
|T1|Complete. Every decision of the session engine and every effect appears in the record: a model request, a tool run, a file write, a program …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T2|Attributed. Every entry names its author and its cause. Only a user's input, a schedule firing or the harness's start has no cause. …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T3|Ordered. Entries of one session have one order. Across sessions, a spawn precedes the child's first entry, a send precedes its delivery, a …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T4|Tamper-evident. Each entry is bound by a hash to all entries before it. Short of a collision of that hash, a record that differs in any …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T5|Crash-clean. After a crash at any point, what an open reads verifies, and holds every acknowledged entry. An anchor is taken only of …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T6|Replayable. Replaying a record gives every decision the answer the record holds, byte for byte, on the same core. A replay causes no effect …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T7|Inputs complete. Everything a decision read is in the record before the decision: no decision depends on a value the record lacks. A replay …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T8|The whole tree. A child's head is anchored in its parent's record at spawn and at each report, and a root's head in the daemon's ledger at …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T9|Audit. One query over a tree answers: for an effect (a write to a path, a program run, a send to a host), which agent did it, by which …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T10|No credential, and redaction keeps the proof. No credential value is in the record. An entry's content can be redacted to its digest: the …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T11|Out of an agent's reach. A write or a delete by an agent that targets a record, an anchor or the ledger is refused, whatever the agent …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|T12|Portable. An exported record verifies and replays with the released verifier alone, to the verdicts its source gives: no daemon, no …|planned (spec only; proposed laws in `spec/record/SPEC.md`)|-|planned|
|O1|Every effect (tool call, subagent spawn, background job, cron fire, heartbeat, queued or steering message, model request, file write) has a …|8 (`laws/once.bend`)|`bend/ffi_once.bend`, `bend/once.bend`, `crates/eukhe-bend/src/rules/once.rs`|law|
|O2|An effect that may change state and whose repeat nothing drops is launched at most once when the world cannot be asked, and takes hold in …|3 (`laws/once.bend`)|`bend/ffi_once.bend`, `bend/once.bend`, `crates/eukhe-bend/src/rules/once.rs`|law|
|O3|An effect is reported done only when it ran (its end returned, or the world shows its effect); not started only when it certainly never ran.|2 (`laws/once.bend`)|`bend/ffi_once.bend`, `bend/once.bend`, `crates/eukhe-bend/src/rules/once.rs`|law|
|O4|A started effect with no end on record, about which the world says nothing, is reported interrupted at the restart: never launched again, …|3 (`laws/once.bend`)|`bend/ffi_once.bend`, `bend/once.bend`, `crates/eukhe-bend/src/rules/once.rs`|law|
|O5|An effect that certainly never ran is launched when its run resumes and reported not started when its run was stopped.|3 (`laws/once.bend`)|`bend/ffi_once.bend`, `bend/once.bend`, `crates/eukhe-bend/src/rules/once.rs`|law|
|O6|An effect ends once; an ended effect never changes and is never launched.|3 (`laws/once.bend`)|`bend/ffi_once.bend`, `bend/once.bend`, `crates/eukhe-bend/src/rules/once.rs`|law|
|O7|A safe effect runs again after a restart. Every launch of a keyed effect carries its idempotency key; it is sent again under that key only …|8 (`laws/once.bend`)|`bend/ffi_once.bend`, `bend/once.bend`, `crates/eukhe-bend/src/rules/once.rs`|law|
|O8|O1-O7 hold at every crash point: after any prefix of a journal's records, and after any list of records at all.|2 (`laws/once.bend`)|`bend/ffi_once.bend`, `bend/once.bend`, `crates/eukhe-bend/src/rules/once.rs`|law|
|O9|The Rust owners keep the journal and act on the core's verdict: a model request's sends in its checkpoint and its `Idempotency-Key`; a …|tests `crash_recovery_e2e::{request, queue_edit, job, tool_once, fire}`, `rlm_children_parent_death_e2e::a_spawn_killed_|-|test|
|D1|An acknowledged commit survives any crash; open reads exactly the complete lines; the log holds a prefix of the commits, in order.|3 (`laws/log.bend`)|`bend/ffi_log.bend`, `bend/log.bend`|law|
|D2|A publish never overwrites a live storage; a sweep never removes a live or young staging directory.|3 (`laws/staging.bend`)|`bend/ffi_staging.bend`, `bend/staging.bend`|law|
|D3|A terminal task never changes; a task's outcome is set once; resume keeps every checkpoint and leaves no task running; joins follow …|20 (`laws/task_life.bend`)|`bend/ffi_task_life.bend`, `bend/task_life.bend`, `crates/eukhe-bend/src/rules/task_life.rs`|law|
|D4|Every run ends; every wait has an exit: a headless run (`-p`, `--mode json`, `--mode rpc`) stops waiting only when nothing runs, nothing is …|8 (`laws/headless_settle.bend`, `laws/run/model.bend`)|`bend/ffi_headless_settle.bend`, `bend/ffi_run.bend`, `bend/headless_settle.bend`|law|
|D5|Honest exit codes: a headless run exits 0 only when it answered, or when the budget ended it after the agent's final answer from the …|14 (`laws/headless_exit.bend`)|`bend/ffi_headless_exit.bend`, `bend/headless_exit.bend`|law|
|H1|Speculation, then effect: a tool runs only for a call of a committed assistant entry; a history with no commit changes nothing; an unsafe …|6 (`laws/tool_call.bend`)|`bend/ffi_tool_call.bend`, `bend/tool_call.bend`, `crates/eukhe-bend/src/rules/tool_call.rs`|law|
|W21|Hand-off at rest. A session started in process can be handed to a daemon, and a daemon session can be taken into a process, when it is idle …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|L1|`/loop [count\|7 (`laws/loop/model.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|L2|Every automatic iteration sends the loop's prompt byte for byte. A prompt the user sends while the loop waits (armed, paused) or between …|3 (`laws/loop/history.bend`, `laws/loop/model.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|L3|The condition is judged on evidence, never assumed. A loop with a condition runs its command after every settled turn and reads only its …|7 (`laws/loop/model.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|L4|A loop is bounded. A count N allows at most N automatic iterations; no iteration starts at or after the deadline of a duration; none after …|17 (`laws/loop/history.bend`, `laws/loop/model.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|L5|A loop is always stoppable. After the user's interrupt (Esc, an abort) no turn and no check starts until the user sends a prompt or …|3 (`laws/loop/history.bend`, `laws/loop/model.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|L6|A loop ends exactly once: it reports its end once, and after the end nothing changes and nothing starts until a new `/loop`.|3 (`laws/loop/history.bend`, `laws/loop/model.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|L7|A loop is durable. Its state (phase, iteration, count left, deadline, condition, prompt, failures, last evidence) is written before each …|9 (`laws/loop/entry.bend`, `laws/loop/history.bend`, `laws/loop/model.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|L8|Queued user messages are not lost and not overtaken: while user input is queued or work is unsettled the loop starts nothing, judges …|2 (`laws/loop/model.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|L9|The user can always see why a loop is still running: its status (`loop_update`, `state.loop`, the tray, `/loop --status`) names the phase, …|3 (`laws/loop/model.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|L10|The loop's decisions run as the compiled core: the entry answers every request Rust spells with the spelling of the model's answer, refuses …|6 (`laws/loop/entry.bend`)|`bend/ffi_loop.bend`, `bend/loop.bend`|law|
|X1|Only an improvement is kept, and every improvement is: a keep is accepted exactly when the run passed, its parsed metric is strictly better …|12 (`laws/autoresearch/events.bend`, `laws/autoresearch/history.bend`, `laws/autoresearch/model.bend`)|`bend/ffi_autoresearch.bend`, `crates/eukhe-bend/src/rules/autoresearch.rs`|law|
|X2|At most one pending run; every started run is logged or abandoned; a refused log changes nothing; the iteration cap stops the loop; the …|13 (`laws/autoresearch/entry.bend`, `laws/autoresearch/events.bend`, `laws/autoresearch/history.bend`, `laws/autoresearch/model.bend`)|`bend/ffi_autoresearch.bend`, `crates/eukhe-bend/src/rules/autoresearch.rs`|law|

## Trees, data marks and the core

Text: Trees, data and core. Ledger: tm11, ds9, ds11.

- ds9 status: partial (outbound scrubber built, off by default: H7; marks planned: C6)
- ds11 status: partial (laws for durable, once, budgets, verified, loop; security, record, orchestration and SDK pillars spec only; --autonomous and --goal without spec)
- Spec rows to write: sr196, sr199, sr36, sr50, sr92, sr215, sr19, sr30, sr67, sr98, sr159

|Row|Requirement|Laws|Code|Status|
|---|---|---|---|---|
|C6|Labels follow data. Data read from a secret place is secret; data from a place the user marked private, or holding a value the scrubber …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|C7|No exit without a capability. An agent sends data labelled L to a destination only when it is allowed a send to that destination with a …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|C13|Declassification is explicit. Only a user's answer releases one labelled value to one destination, once. Any other value, destination or …|planned (spec only; proposed laws in `spec/security/SPEC.md`)|-|planned|
|H7|The outbound scrubber (`privacy.anonymizeRemote`) rewrites no code and keeps every token it can restore: a text is an IP address exactly …|49 (`laws/privacy/entry.bend`, `laws/privacy/ip.bend`, `laws/privacy/token.bend`)|`bend/ffi_privacy.bend`, `crates/eukhe-bend/src/rules/privacy.rs`|law|
|R2|Every subagent reports exactly once; no credential reaches a child.|18 (`laws/child/entry.bend`, `laws/child/exact.bend`, `laws/child/model.bend`, `laws/child/run.bend`, `laws/child_env.bend`)|`bend/child.bend`, `bend/child_env.bend`, `bend/ffi_child.bend`, `bend/ffi_child_env.bend`|law|
|M3|Each session is its own thread: a session's request holds only its own thread's messages; the newest turns are present verbatim until …|12 (`laws/thread.bend`)|`bend/ffi_thread.bend`, `bend/thread.bend`, `crates/eukhe-bend/src/rules/thread.rs`|law|
|pillar:durable|every requirement of Eukhe's durable pillar (spec `durable/log.bend`, `durable/task_life.bend`, `durable/task_life_wire.bend`, …|law areas log (34), staging (35), listing (14), tree (41), task_life (27), job (39), job_step (22), wait (23), headless_settle (15), headless_exit (36), …|`bend/`, `crates/eukhe-bend/src/rules/` per area|law|
|pillar:once|every requirement of Eukhe's once pillar (spec `once/life.bend`)|law areas once (27)|`bend/`, `crates/eukhe-bend/src/rules/` per area|law|
|pillar:budgets|every requirement of Eukhe's budgets pillar (spec `budget/ledger.bend`)|law areas budget (45), budget_share (15)|`bend/`, `crates/eukhe-bend/src/rules/` per area|law|
|pillar:verified|every requirement of Eukhe's verified pillar (spec `verified/verify.bend`, `verified/verify_wire.bend`)|law areas verify (48)|`bend/`, `crates/eukhe-bend/src/rules/` per area|law|
|pillar:loop|every requirement of Eukhe's loop pillar (spec `loop/loop.bend`)|law areas loop (57)|`bend/`, `crates/eukhe-bend/src/rules/` per area|law|
|W1|One written contract. Every frame the daemon sends or accepts is described by one schema with a version, and on a connection every frame …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W2|Negotiation. The daemon's hello states the range it speaks and its capabilities; the client states its range. The connection speaks the …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W3|Old client, new daemon. A client built against any release in the window works with every later daemon whose range holds its version: the …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W4|New client, old daemon. A client works with every daemon in the window: for each feature the daemon has, as above; a feature the daemon …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W5|Minors only add. Within a major a release may add a command, an optional field, an event, an enum value, an error code, and each such …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W6|Unknown is tolerated. A receiver ignores a field it does not know, unless the frame lists it as critical (W7), and keeps it when it stores …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W7|Critical is never ignored. A sender lists in the frame each field whose silent loss would be unsafe. A receiver refuses whole, with nothing …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W8|Deprecation. A feature is removed only at a major, and only after every release of the notice period marked it deprecated; a history that …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W9|Durable formats. A build reads every format an older build of the window wrote: every field the older format held reads back with the value …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W10|Errors and order are part of the contract. Error codes are stable names; their text is not. Every command gets exactly one response with …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W11|SDKs. Each official SDK is generated from the schema, states the range it speaks, and works with any daemon whose range meets it. Process …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W12|Upgrade is safe. Replacing a daemon by a newer build never ends a session's work: only an idle daemon is replaced. After it, an attached …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W13|Proven by a matrix. Process rule, no law: each release is tested against the clients and daemons of every release in the window, both ways, …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W14|One API, two doors. The SDK has one API for both doors. The host chooses the door with one connect option: in process with its agent dir, …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W15|One event stream. Both doors deliver the same events: the wire's session event vocabulary, with the same per-session cursor (generation, …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W16|Host callbacks in both doors. Host tools, approvals, budget questions and cancellation are given once, as the same callbacks, whichever …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W17|Host-callback protocol. Through the daemon, a host registers its callbacks for a session under its host id: each tool with its name and …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W18|A daemon session outlives its host. When a host detaches, the session keeps running. A call pending to that host stays pending for the …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W19|Cancellation means the same in both doors. Every SDK call takes the host's cancellation token. Cancelling it ends that call: the run a …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W20|The door changes lifetime and sharing, not meaning. The daemon door adds what a separate process gives: sessions that survive the host's …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W21|Hand-off at rest. A session started in process can be handed to a daemon, and a daemon session can be taken into a process, when it is idle …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W22|Compatibility laws apply to both doors. Through the daemon the SDK is a client like any other: W2 to W4, W6 to W8, W10 and W12 hold for it, …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|
|W23|Proven the same. Process rule, no law: one host program, run against both doors on the same scripted model, gives equal event streams and …|planned (spec only; proposed laws in `spec/contract/SPEC.md`)|-|planned|

## The bet

Text: The bet. Ledger: tm12, ds13, bet.

- ds13 status: gap (input origins exist; no decision cause recorded)
- Spec rows to write: sr37, sr42, sr49, sr52, sr61, sr88, sr162, sr166, sr173, sr185, sr187, sr188

## Totals

design: 14, law: 64, law (branch; no Rust runs it): 13, planned: 71, test: 5 (a row cited by two pillars counts twice).
