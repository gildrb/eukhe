# Agent tree

Status: design, proven Bend model and core entry (`bend/agent_tree.bend`,
`bend/agent_crown.bend`, `bend/ffi_agent_tree.bend`, laws
`laws/agent_tree.bend`, `laws/agent_crown.bend`, requirements T1-T14 in
`spec/README.md`). No Rust calls it yet; section 9 lists the Rust work.

The agent tree is how one task runs on several agents at once. Every node
of the tree is one agent. A node either does its work alone (a leaf) or
splits into exactly two children and becomes their parent: it gives each
child a disjoint part of its scope, keeps working on its own part,
integrates the two results when they arrive, checks them and reports up.
A child may split again, so the tree grows one level per split: one task,
then two, then four.

## 1. Eukhe today

|Area|Today|Where|
|---|---|---|
|spawn|`rlm.spawn` / `rlm.spawn_batch` from the kernel; a reason (`parallel`, `isolate`, `tools`, `user`), depth below `rlmMaxDepth` (3), family below `subagentMaxConcurrency` (32); a batch all or none|`bend/family.bend` (R1), `crates/eukhe-core/src/durable/children/`|
|workspace|`shared` (the parent's directory) by default, or `isolated`: a copy-on-write copy|`crates/eukhe-core/src/durable/children/child_workspace/`|
|merge|an isolated child's files come back path by path at its end; a file both sides changed keeps the parent's bytes and the child's go to `conflicts/`; shared children rely on the per-path lock and the publish re-check (H4, H10)|`bend/sandbox.bend`|
|results|one report per child as a follow-up input (R2); the parent reads with `rlm.collect`, `rlm.answer` or `jobs.wait`|`bend/child.bend`|
|budget|one account per tree with holds and final-answer reserves (B1-B14); a child named a `budget` gets it carved from its parent|`bend/budget.bend`, `bend/budget_share.bend`|
|cancel|closing a session closes its children first, recursively; an abort of the parent's turn reaches background children only with `background: true`|`bend/task_life.bend`|
|visibility|the agents panel nests running subagents by depth|`crates/eukhe-tui/src/agents_panel.rs`|

Gaps the tree closes:

1. No scope per child: two children may write the same file; the clash
   shows only at merge, and the parent's bytes win.
2. A spawn is a flat batch: nothing says how a task divides, so a large
   task either runs on one agent or fans out without structure.
3. Integration runs in the parent's own turn, serially, after it waited
   for every child; the parent idles while children run.
4. A child's limit is either the shared account or a fixed carve; a
   settled child's unspent limit is not handed back to its parent's free.
5. No rule says a parent finishes only after its children settled, and an
   abort of the parent's turn can leave children running.

## 2. Why disjoint isolated scopes do not conflict

Five mechanisms, each stated as a rule of the tree:

1. **Snapshot of the live tree.** A child's checkout is a copy-on-write
   copy of its parent's working tree at the split, uncommitted edits
   included. The child starts from what the parent sees.
2. **Baseline from the child's own copy.** The child's patch is the diff
   of its checkout against the copy's start, never against the live
   parent: other children's integrations never leak into it. The checkout
   is a git repository of its own whose one commit is that start: `git
   status` and `git diff` there show the child's changes only. It holds
   nothing of the parent's repository (history, branches, remotes), and
   the patch never carries its `.git`.
3. **Disjoint scopes, checked at the split.** The split names each child's
   scope; the core admits it only when own, left and right partition the
   parent's scope (T1, T2). Two running nodes never own the same unit.
4. **Integration by ownership.** The parent takes from a child's patch
   exactly the units of the child's scope; a write outside is a conflict,
   reported and never applied (T3). Disjoint scopes commute, so arrival
   order does not matter (T4) and the parallel result equals one agent
   doing every patch in order (T5).
5. **Asynchronous results.** A split returns at once; results arrive as
   inputs; the parent keeps working on its own scope and integrates each
   result when it lands (T10).

## 3. Node

|Field|Meaning|
|---|---|
|status|`Running`, `Finished`, `Failed`, `Cancelled`; the last three are settled|
|scope|the units (paths) the node owns|
|limit|`Unlimited` (the default run: until finished) or a value|
|spent|what the node itself spent|
|deadline|`Unlimited` or a wall-clock time|
|patch|a leaf: its work; a split: its own work and its integration fixes|
|own|a split only: the part of its scope it keeps for itself|

A unit is a path. Rust maps the paths of a split to positions: a scope is
a mask over them. A file created later belongs to the scope of its nearest
owned directory.

## 4. Life of a node

```
           work alone
 Running ───────────────► Finished(patch)
    │ split(own, L, R)
    ▼
 Running split ── integrate L, R as they settle; work on own ──► Finished(patch)
    │ fail(partial)                         ▲ only when L and R settled
    ▼                                        │
 Failed(partial)  ── children cancelled      │
 cancel / deadline ──► Cancelled, subtree cancelled
```

Events, each addressed by a path (left/right steps from the root):

|Event|Admitted when|Effect|
|---|---|---|
|`split(own, ls, rs, hold)`|running leaf; depth + 1 <= `max_depth`; nodes + 2 <= `max_nodes`; own, ls, rs partition the scope, each child owns a unit; room >= hold + 2|two running leaves; limits: the halves of room - hold; deadline: the parent's less the margin|
|`spend(a)`|running; a <= room|spent += a|
|`finish(patch)`|running; a split only when both children settled|`Finished`|
|`fail(partial)`|running|`Failed` with the partial patch; subtree cancelled|
|`cancel`|always|every running node of the subtree `Cancelled`|
|`redo(side, extra)`|running split; that child a failed or cancelled leaf; extra <= room|the child runs again: same scope, spend, deadline and partial patch; limit spent + extra|
|`tick(now)`|always|every running node whose deadline is up, and its subtree, `Cancelled`|

A refused event changes nothing and names its first failing check
(`NoNode`, `NotRunning`, `NotLeaf`, `TooDeep`, `TooMany`, `BadScopes`,
`NoBudget`, `Unsettled`, `NotRedoable`).

Room: `limit - spent - held(left) - held(right)`; a running child holds
its limit, a settled child what its subtree spent. So a child's unspent
limit returns to its parent when it settles. `Unlimited` less anything is
`Unlimited`; its halves are `Unlimited`; no tick cancels an `Unlimited`
deadline.

Failure: a failed child returns its partial patch and its reason. The
parent decides: `redo` (the child runs again from its partial work), or
absorb (the parent writes the child's scope itself: a settled child's scope
joins the parent's write scope).

### Help leaves

Writers form the binary tree; read-only helpers are extra leaves
(`bend/agent_crown.bend`, T14). A running node asks one with `help(a)`: it
is admitted when the node runs, the tree's nodes plus the help leaves plus
one fit `max_nodes`, and `a` fits the node's room on the view (below);
its limit is `a` (`Unlimited` under an `Unlimited` room), its deadline the
node's less the margin. A help leaf has no write scope: integrating its
patch applies nothing, and every unit it wrote is a conflict. It spends
within its limit and settles (`Finished` or `Failed`) while running.

A help leaf charges its node: while running its limit (an `Unlimited` one
nothing), once settled what it spent. Every tree event is decided on the
view, the tree with each node's spent raised by the charges at its path,
under `max_nodes` less the help leaves; the charges are then taken off
again, and every running help leaf whose node no longer runs (cancel,
fail, finish, a tick above it), or whose own deadline a tick finds up, is
cancelled. A help leaf never blocks its node's finish. In every reachable
crown no running help leaf sits at a node that does not run, nodes plus
help leaves stay within `max_nodes`, and under a `Value` root limit the
tree's spend plus the help leaves' fits it. With no help leaf a tree event
is exactly the tree's step, so T1-T11 carry over.

## 5. Integration

The parent's view of a child's result is a patch over units. Integrating
it overlays the child's writes inside the child's scope on the parent's
patch; writes outside are conflicts (T3).

1. A result arrives (the child settled). Rust computes its patch from the
   child's checkout against the checkout's start.
2. The core overlays it (`overlay`), returns the conflicts.
3. The parent sees the integrated patch, the conflicts and the child's
   report; it resolves conflicts inside its own write scope (own plus its
   settled children's scopes), runs the narrowest check that covers the
   two scopes, and either finishes or keeps working.

The integrated patch of a subtree (`result`): the two children's results,
each computed alone from the same base, overlaid left then right, then the
node's own patch. T5: for a tree whose patches stay in their scopes, this
gives the files that one agent gets applying every patch in post-order.

## 6. Scheduling a node

Next action (T10), first that applies: read the user's message; integrate
an arrived result; work on own scope; wait. A node waits only with nothing
to do, and a user message always comes first.

## 7. Bounds

`max_depth` and `max_nodes` are configured; every reachable tree keeps
both (T9). A balanced tree with 2^d leaves has depth d: 8 slices = 3
levels, 15 nodes. A one-sided tree reaches depth (n - 1) / 2 with n nodes,
so `max_depth` is its own bound.

## 8. Cost and experiment

Depth costs a planning round per level: before a node's children start,
the node plans its split (one model turn), and before it reports, it
integrates (one turn plus a check). For n independent slices of work w
each:

|Shape|Levels|Wall time|Planning turns|
|---|---|---|---|
|one agent|0|n·w|0|
|binary|log2 n|log2 n·(p + 2i) + w|n - 1|
|k-way|logk n|logk n·(p + k·i) + w|(n - 1)/(k - 1)|

p: one planning turn; i: integrating one child result (apply, check);
estimates, to be replaced by the measurements below. 8 slices: binary 3
levels and 7 splits, 8-way 1 level and 1 split.

The tree is binary (the owner's decision). The experiment measures what
that costs against a wider split, as information:

1. Tasks: 4 repository tasks, each with 2, 4, 8, 16 independent slices
   (one file group per slice, a test per slice).
2. Arms: binary tree; 4-way; flat (one split into n); one agent.
3. Runs: headless (`eukhe -p`, limits off), 5 per task and arm, the same
   model and seed list; integration checks on.
4. Measures from the spawn ledger and the budget ledger: wall time to the
   root's report; input and output tokens; model requests; conflicts at
   integration; failed children and redos; final check result.
5. Report: median and spread per slice count and arm, and the crossover
   slice count where a wider split wins on wall time or tokens.

## 9. Rust

1. Core entry `bend/ffi_agent_tree.bend`, id 461 `agent_tree` in
   `bend/core_entries.txt` (T13), called through
   `crates/eukhe-bend/src/rules/agent_tree.rs`: the crown's `hstep`,
   `overlay` and `conflicts`, `next`, `cfree`.
2. `rlm.split` for a node (`crates/eukhe-core/src/durable/children/spawn.rs`):
   own scope, two (scope, task) pairs, hold. Scope paths resolve to units
   (`child_workspace/units.rs`); the core admits or refuses. A help leaf is
   `rlm.spawn` without a write scope. Every node reads the split rule in
   its own system prompt (`prompts/layers/core.md`) and, in its
   `session-role` section, its place: its scope, and whether it may split
   with the levels and agents left below it (`tree::split_room`). A child
   splits again by its own prompt, never by text its parent relays: in the
   first Haiku grid, children that knew neither their scope nor their room
   never split again.
3. Each writing child works in a copy-on-write checkout of the parent's
   live tree (the `isolated` workspace), its patch computed against its own
   start; a failed child's partial patch is measured too.
4. Results arrive as inputs; integration by `overlay` (a scoped hand-back),
   conflicts to the parent. The integration runs at the child's end,
   before any check: the parent's workspace and the child's row
   (`rlm.collect`) hold the child's work at once, its checks marked to
   come. Then the project's check runs in the child's checkout and after
   integration (`agentTree.checkCommand`, `agentTree.checkTimeoutSecs`;
   `child_workspace/check.rs`), and the report carries both. A running
   check reports its start, every 30 s its elapsed time and last output
   line, and its end (`check_update` events: the TUI status line, a
   headless run's stderr and json stream). A failed check's verdict names
   its last 3 output lines. The integration check runs in the live tree,
   unfrozen (a copy lacks the build caches and dependency dirs); stamps
   before and after it (one `lstat` per listed path,
   `child_workspace/stamp.rs`) name each path written meanwhile in its
   report. A detached `bash` job's result names them the same way.
5. Budget: each child's limit from the split; room, holds and the return
   of unspent limits through the existing ledger (B4, B13). The session's
   crown (`durable/children/tree/`) records each child's spend and end.
6. Cancel on abort (`cancel_tree`), tick on the child task's clock.
7. `jobs.wait` and `rlm.collect` end on the tree's next action (T10).
8. TUI: the agents panel and the swarm block draw one row per node: role,
   status, scope, elapsed, cost (T12).
9. The experiment of section 8.

## 10. Laws

`laws/agent_tree.bend`, one line each; coverage per requirement in
`spec/README.md`.

|Req|Law|States|
|---|---|---|
|T1|`agent_tree_split_is_spec`|a split is decided exactly as the spec: checks in order, the new split node, nothing else changed|
|T1, T8|`agent_tree_halves_fair`, `agent_tree_halves_unlimited`|the halves add up and differ by at most one; Unlimited halves are Unlimited|
|T2|`agent_tree_tiles_root`|every reachable tree's own and leaf scopes own each unit as often as the root's scope|
|T3|`agent_tree_overlay_applies`, `agent_tree_conflicts_cover`, `agent_tree_conflicts_outside`, `agent_tree_result_integrates`, `agent_tree_result_leaf`, `agent_tree_apply_lands`, `agent_tree_apply_ends`, `agent_tree_apply_past_end`|integration applies exactly the in-scope writes, in a split's integrated patch too (tidy tree or not); a leaf hands up its whole patch, a stray write never dropping the rest; every other write is a conflict; a conflict is never in scope; applying a patch sets each written unit to its new bytes and keeps every other unit, those past the patch's end too; a patch longer than the files adds no unit|
|T4|`agent_tree_arrival_commutes`|disjoint scopes: either arrival order gives the same files|
|T5|`agent_tree_parallel_is_sequential`|the tree's integrated patch gives the files of every patch applied in post-order|
|T6|`agent_tree_finish_is_spec`, `agent_tree_no_orphan`, `agent_tree_done_settled`|a split finishes only after both children settled; no running node under a settled one|
|T7|`agent_tree_cancel_quiets`, `agent_tree_cancel_marks`, `agent_tree_cancel_keeps`, `agent_tree_cancel_shape`, `agent_tree_cancel_needs_node`, `agent_tree_cancel_takes`, `agent_tree_cancel_frame`, `agent_tree_fail_quiets`, `agent_tree_fail_marks`, `agent_tree_fail_shape`, `agent_tree_fail_frame`, `agent_tree_fail_needs_running`, `agent_tree_fail_needs_node`|cancel and fail stop the whole subtree and nothing else; a cancel, and a fail below the failed node, marks running nodes Cancelled, keeps settled ones and changes nothing in the subtree but statuses (shape, own scopes, every info); a failed node keeps its partial patch and its spend; a cancel or a fail at a missing path is refused NoNode, a cancel at a node that is there is always taken|
|T8|`agent_tree_spend_is_spec`, `agent_tree_info_reads`, `agent_tree_spend_binds`, `agent_tree_init_admits`, `agent_tree_init_deadline`, `agent_tree_init_unspent`, `agent_tree_init_blank`, `agent_tree_budget_holds`, `agent_tree_deadlines_down`, `agent_tree_tick_none_late`, `agent_tree_tick_keeps_on_time`, `agent_tree_tick_cancels_only_late`, `agent_tree_tick_cancels_late_below`, `agent_tree_tick_shape`, `agent_tree_tick_marks`|spends within room; spends add up (a later spend sees the earlier ones; the code reads every node field as stored); the root starts as a running leaf with the configured scope, limit and deadline, nothing spent and nothing written; the tree's spend fits the root's limit; deadlines never rise going down; a tick cancels the late nodes and their subtrees (marked Cancelled, never Finished or Failed) and changes nothing but statuses, and no node on an on-time path; in any tree, whatever the deadlines below a late node, nothing under it runs after the tick|
|T9|`agent_tree_depth_bound`, `agent_tree_nodes_bound`, `agent_tree_depth_configured`, `agent_tree_nodes_configured`, `agent_tree_split_reads_bounds`, `agent_tree_split_margin_both`, `agent_tree_depth_reads_config`, `agent_tree_nodes_reads_config`, `agent_tree_margin_reads_config`|reachable trees stay within both bounds as configured; the configured bounds and margin apply to both children; every split check reads the bounds as configured, so deeper splits the configuration allows are admitted|
|T10|`agent_tree_next_waits_iff_idle`, `agent_tree_next_message_first`, `agent_tree_next_integrates_first`, `agent_tree_next_works_own`|the next action's order; a wait only with nothing to do|
|T11|`agent_tree_redo_is_spec`|a redo is decided exactly as the spec|
|T13|`agent_tree_entry_answers`, `agent_tree_entry_reads`, `agent_tree_entry_exact`, `agent_tree_entry_refuses`, `agent_tree_entry_example`|the core entry `bend/ffi_agent_tree.bend` (id 461) answers every request Rust spells (a step of the crown, an overlay, a next, a free) with the model's decision and refuses any other input with `E agent_tree: malformed request`|
|T14|`crown_help_is_spec`, `crown_free_is_spec`, `crown_help_spend_is_spec`, `crown_help_end_is_spec`|a help, the free reported at a node, a help leaf's spend and its end are decided exactly as the spec: checks in order, the help leaf appended or changed, the tree unchanged; the free is the view's room|
|T14|`crown_tree_is_spec`, `crown_tree_alone`, `crown_init_steps_as_tree`, `crown_init_root`|a tree event is the tree's step on the view under `max_nodes` less the help leaves, the charges taken off again, orphaned or late help leaves cancelled; with no help leaf exactly the tree's step; a run starts from one running root with the configured scope, limit and deadline and no help leaf|
|T14|`crown_help_overlay_nothing`|a help leaf's patch applies nothing; every unit it wrote is a conflict|
|T14|`crown_never_blocks`|a finish is taken exactly when the tree's step on the view takes it; after it no help leaf at the node runs|
|T14|`crown_no_orphan`, `crown_nodes_bound`, `crown_budget_holds`; "reachable": `crown_run_none`, `crown_run_last`|in every reachable crown running help leaves sit at running nodes, nodes plus help leaves fit `max_nodes`, and under a Value root limit the tree's plus the help leaves' spend fits it|
|T15|`work_list_finished_exactly_all_done`, `work_list_left_exactly_open`, `work_list_left_in_order` (`laws/work_list.bend`)|a child given items (a split half, an `rlm.spawn` help leaf or a worker's task) hands back finished exactly when every item is accounted done; else stopped, naming each item left once, in the parent's order|

Mutation probe (`mutate.py` on `bend/agent_tree.bend`): every mutant is
killed or stillborn but four, all equivalent:
each swaps the two arguments of a `Bool.or` or `Bool.and` in `cell`, and
both are commutative, so the mutant returns the same Bool on every input.
On `bend/agent_crown.bend` one survives, also equivalent: `hscope`'s body
replaced by `Nil{}` is the body it already has (`[]`).

## 11. Decisions

1. `max_depth` 3, `max_nodes` 15; margin per level 2 min under a
   deadline, 0 when Unlimited. R1's spawn reasons and family cap retire
   with the old spawn path.
2. A unit is a file. Shared files (lockfiles, `mod.rs`, generated code)
   are the parent's own scope; a child that needs one reports a conflict.
3. A child's checkout is the existing `isolated` copy-on-write workspace:
   a snapshot of the live tree, uncommitted edits included; its patch is
   the diff against its own start.
4. The harness overlays each result; the parent resolves conflicts and
   runs the project's configured check command, else the narrowest check
   detected for the touched files (the tests of the touched crates or
   packages).
5. Each child's check runs in its checkout after its integration, before
   its report; the parent checks again after integration.
6. One spawn path: every subagent is a tree node; a tool-less or
   read-only child is a leaf with an empty write scope.
7. Split only with two halves on disjoint files, each worth a planning
   turn.
8. Hold: max(two worst-case requests, 10% of room); one automatic redo
   per child.
9. A failed child's partial patch is applied only when the parent absorbs
   it.
10. Experiment: 3 tasks, 2, 4, 8 slices, binary against wide, 3 runs each
    on a small model at low effort; the two best arms once more each on a
    large model; $25 cap.
11. The tree view replaces the agents panel's nesting.
