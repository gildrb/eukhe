# orchestration (spec): orchestration at scale

Status: spec only. Nothing below is implemented; no law named in section 4
exists yet. Ids `O1..O14` are provisional.

Many agents, loops and workflows run at once and nobody watches them. Each
gets its turn; none waits forever; no two wait on each other; no message is
lost or delivered twice; every queue has a bound and says so when it is
full; nothing starts past a limit. The pillar builds on provider admission,
the family cap, the workflow scheduler, the waits, the jobs, the session
tree and the kin rule; it adds what is missing: one scheduler across trees,
fairness, bounds on every queue, a wait-for rule across agents, and a
bounded mailbox with returns.

## 1. Words

- **unit**: anything that asks to run: a session's turn, a subagent, a loop
  iteration, a workflow step, a background job, a model request.
- **tree**: a root session and all its descendants. The tree is the
  **tenant**: fairness is between trees, order inside a tree.
- **class**: interactive (a person waits) or background.
- **limit**: a number of units that may run at once, per scope: the daemon,
  a tree, a provider. A unit **counts** under every limit on its path while
  it runs; a unit blocked in a wait does not count (O9). **admit**: start a
  unit, counting it under all its limits in one step, or under none.
- **eligible**: a waiting unit that every limit on its path has room for,
  with no earlier unit of its tree and class that needs the same limits
  still waiting. **passed**: an eligible unit is passed each time another
  unit is admitted while it is eligible.
- **queue**: where units or messages wait. **bound**: the most a queue
  holds. **mode**: what a queue does at its bound: **refuse** (answer
  "full" at once, changing nothing) or **hold** (keep the sender waiting
  until there is room).
- **message**: bytes from one agent to another, with an id. **accepted**: the
  sender got an acknowledgement. **delivered**: the target's context has it.
  **returned**: the sender is told it could not be delivered, and why.
- **wait-for**: a waits for b when a cannot go on until b does something.
- **act**: a tool call with its result, or an accepted progress note (the
  work ledger of `bend/progress.bend`).

## 2. Requirements

|Id|Requirement|
|---|---|
|O1|Admission. A unit starts only when every limit on its path has room: the daemon's, its tree's, its provider's. A unit, or a batch as a whole, that cannot start waits in its tree's queue; when that queue is at its bound it is refused instead. A refusal comes in the step of the offer, names the full queue and a limit that had no room, and changes nothing, so a retry is safe.|
|O2|Slots are conserved. The units that count under a limit never exceed it. A unit that ends, is stopped, or whose process dies stops counting under every limit on its path, once, and in that same step the freed room goes to eligible units.|
|O3|Every queue is bounded. Each queue has a declared bound it never passes and a declared mode at the bound. Below the bound an offer that cannot be served at once is queued, never refused. Nothing is dropped in silence: every unit offered is waiting, running, ended, withdrawn or refused; every message is as O7 says.|
|O4|No starvation between trees. An eligible unit is passed by at most a bounded number of admissions of its own class from other trees (one per other tree, for equal weights), whatever the others queue. Inside a tree, units of one class that need the same limits start in the order they arrived.|
|O5|Interactive first, background still served. While an interactive unit is eligible, a background unit is admitted ahead of it only when it is the oldest eligible background unit of that scope and a bounded number of interactive admissions were made since a background unit last went ahead so. So background work passes a person's turn at most once per bound, and the oldest background unit never waits forever.|
|O6|Work-conserving. After every step no waiting unit is eligible: room and a unit that could use it never both remain.|
|O7|No lost message. An accepted message is delivered to its target exactly once, or returned to its sender with the true reason (the target ended, was deleted, or refused it). A busy target queues it; a target that becomes idle takes its oldest queued message in that step; a parked one is woken. A crash of either side loses none.|
|O8|No duplicate, in order. A message redelivered after a crash or a retry is recognised by its id: the target sees each id once. Messages from one sender to one target are delivered in the order they were accepted; a report never overtakes what its sender sent before it.|
|O9|No deadlock. The wait-for relation among agents, loops, workflows and tasks never holds a cycle: a wait that would close one is refused with the cycle, and a message to an agent that waits on its sender ends that wait. A unit is counted under all its limits in one step or under none. A unit blocked in a wait counts under no limit, so what it waits on can start; when the wait ends it is admitted again ahead of every unit that arrived after it began to wait.|
|O10|Every wait has an exit. A wait is accepted only when something it watches still runs or it has a deadline; a wait on nothing is refused at once. When the last thing a wait watches ends or dies, the wait ends in that step. A running unit that records no act within its stall bound is ended and stops counting; a unit waiting in a queue or in a wait is never ended as stalled.|
|O11|Stopping scales. Stopping an agent ends exactly the units of its subtree, within a bound that grows with the subtree's size. Outside the subtree nothing changes but what follows from it: the freed room goes to eligible units, its undelivered messages return to their senders, waits on its agents end.|
|O12|Control is never queued. A status request is answered in the step it arrives, with the true state; a stop takes effect; neither takes a slot or a place in a queue. A saturated daemon can always be inspected and stopped.|
|O13|A slow reader hurts only itself. What a client receives depends only on the events and on its own reading: a client that reads slowly never delays an agent and never changes what another client receives. A client that lags less than the ring holds receives every event; past that, what it missed is marked as a gap with its range, and the gap can be read back exactly from the record.|
|O14|Survives restart, and is visible. After a daemon restart the scheduler's state is rebuilt from durable state: no unit lost, none admitted twice, order kept, dead holders no longer counted. For every waiting unit a client can read why it waits: a limit that is full, its place in the order, the units that hold that limit; each of them true.|

## 3. What exists in eukhe

### eukhe (origin/merge/main-into-client-sdk)

|Area|What it decides today|Where|
|---|---|---|
|provider admission|Per provider: at most `providerMaxInFlight` requests; FIFO per class; a background request only while no interactive one holds or waits; on a capped provider an interactive request preempts background holders; past `providerMaxQueued` (64) the next request fails at once.|`bend/admission.bend`, `laws/admission.bend` (`admission_capacity`, `admission_fifo`, `admission_no_lost_wakeup`, `admission_preempts`, `admission_every_ticket_ends`), `crates/eukhe-core/src/admission.rs`|
|family|A spawn needs a reason, depth below `rlmMaxDepth`, the family's running subagents within `subagentMaxConcurrency` (32); a batch all or none; refusal order fixed.|`bend/family.bend`, `laws/family.bend` (R1)|
|workflow|A run's concurrency semaphore, agent budget, resume cache; a failure spares siblings.|`bend/workflow.bend`, `laws/workflow/` (56)|
|sub-model calls|`rlm.query` batches: budget, then concurrency cap, then waves covering every call once, in order.|`bend/rlm_query.bend` (R3)|
|messages|An agent messages only its parent and its children; an admitted message is queued, taken or wakes a parked target, never dropped.|`bend/kin.bend`, `spec/agents/kin.bend` (A3)|
|reports|Each subagent reports exactly once; the report is resubmitted under a new id when withdrawn; a stalled or unreachable child is detected.|`bend/child.bend`, `laws/child/` (R2)|
|submissions|A submission is queued, placed, then done or unanswered, and never moves back.|`bend/submission.bend`|
|waits|A wait ends once, by its event, its deadline or a cancel; a wait-any is refused when nothing runs, capped at 30 minutes; a settled job's result is delivered once.|`bend/wait.bend`, `bend/wait_any.bend`, `spec/durable/wait_any.bend` (D4)|
|tasks|Joins follow failFast or allSettled; an abort marks exactly the owned live tasks; the durable scheduler keeps its wait-for graph acyclic (Rust).|`spec/durable/task_life.bend` (D3), `crates/eukhe-durable/src/harness/scheduler/execution.rs:497-578`|
|jobs|A job's feed, kill and blocking wait; whether its end wakes the session.|`bend/job.bend`, `bend/job_notice.bend` (D6)|
|supervisor|Restart budget with backoff; an orphaned worker hands its work over; busy evidence and boot revival; idle shutdown commits only when every gate is closed.|`bend/supervise.bend`, `bend/orphan.bend`, `bend/revive.bend`, `bend/launcher.bend`|
|daemon back-pressure|One worker accepts 128 in-flight requests, then answers `worker_overloaded`; a client connection runs 64 commands and holds 32768 outbound frames; the event ring holds 4096 and drops for a reader that lags; control routes and watches take no permit.|`crates/eukhe-daemon/src/backpressure.rs` (Rust only, no law)|

Gaps against the requirements:

1. No limit across trees and no fairness. Provider admission is one FIFO
   per class for the whole daemon: a tree that queues a hundred requests
   is served before another tree's first (O4). On a capped provider a steady
   interactive load keeps every background request waiting
   (`admission_background_yields`) (O5).
2. No daemon-wide limit on live agents or workers: each active session is a
   process, and only the per-family cap bounds them (O1).
3. Queues without a bound: the session inbox (`pi.inbox`) and the kin
   queue of a busy target. The daemon's bounds are Rust constants with no
   law (O3, O12).
4. A reader that lags loses events: the ring drops them, and a resume
   cursor that is not at the end answers `event_replay_not_available`
   (`crates/eukhe-daemon/src/protocol.rs:447`) (O13).
5. Wait-for is checked inside one session's tasks only. Across agents no
   rule exists: a parent blocked in a wait on its child while the child's
   question waits on the parent is not ruled out by a law (O9).
6. A message to an agent that has ended has no stated fate (O7); order
   between a child's messages and its report is not stated (O8).
7. After a restart, queues are rebuilt by each worker alone; no law states
   the order is kept (O14).

## 4. Proposed laws (requirement laws only)

All are stated over steppers whose events an adversary orders (arrive,
end, cancel, crash of a holder, wait, stop, tick), as `laws/admission.bend`
does.

|Req|Law|States|Rejects|
|---|---|---|---|
|O1|`sched_admit_iff_eligible`|A unit is admitted in a step exactly when it is eligible and the order of O4 and O5 picks it among the eligible units.|A check of the provider's limit only.|
|O1|`sched_batch_whole`|A batch is admitted whole, queued whole, or refused whole with the state unchanged.|Half a batch running.|
|O1|`sched_refusal_exact`|A refusal is among the outputs of the step of its offer, the queue it names is at its bound and the limit it names has no room, and the state is unchanged.|"Queue full" a tick later; a refusal that names a limit with room.|
|O2|`sched_counted_within_limits`|In every reachable state, for every scope, the units that count are at most its limit, and the trees' counts sum to at most the daemon's.|A crash that leaks a slot; a preemption counted twice.|
|O2|`sched_end_uncounts_once`|The end, stop or crash of a running unit lowers the count of exactly the scopes on its path by one; the end of a unit that already ended changes nothing.|An end that marks the unit and frees nothing; a stop and a natural end both releasing.|
|O3|`queue_within_bound`|In every reachable state each queue holds at most its bound.|A wake path that pushes without the check.|
|O3|`queue_below_bound_queues`|An offer that cannot be served at once while its queue is below the bound is queued; at the bound the queue's declared mode is applied: a refusal, or a held sender that is served, in order, when room appears.|A scheduler that refuses whatever it cannot start, so fairness has nothing to order.|
|O3|`queue_fates_conserved`|In every reachable state each offered unit is exactly one of waiting, running, ended, withdrawn or refused: offered = waiting + running + ended + withdrawn + refused.|Drop the oldest on overflow; a cancelled unit that vanishes.|
|O4|`fair_bounded_bypass`|An eligible unit is passed by at most a bound of admissions of its own class from other trees (one per other tree for equal weights) before it is admitted, whatever the others enqueue.|One FIFO across trees; shortest queue first.|
|O4|`fair_tree_fifo`|Two units of one tree and class that need the same limits are admitted in arrival order.|A retry that jumps the queue.|
|O4|`fair_share`|Over any run of k admissions of one class during which every tree has an eligible unit of that class, each tree gets at least its weighted share of k, less one.|Round robin that restarts at the first tree after each release.|
|O5|`prio_interactive_first`|A background unit is admitted in a step where an interactive unit of its scope is eligible only when it is the oldest eligible background unit there and the bound of interactive admissions was made since the last such step.|Background admitted by arrival order; fifty aged background units admitted in a row.|
|O5|`prio_background_bounded`|The oldest eligible background unit of a scope is passed by at most the bound of interactive admissions.|Strict priority (today's rule on a capped provider).|
|O6|`sched_work_conserving`|After every step no waiting unit is eligible; this carries `admission_no_lost_wakeup` to every scope.|A release that wakes only its own tree.|
|O7|`mail_conserved`|In every reachable state, crashes included: accepted = queued + delivered + returned, and each accepted id is in exactly one of them.|A full mailbox that discards; a target's end that forgets its queue.|
|O7|`mail_idle_delivers`|In the step a target becomes idle with messages queued, its oldest is delivered; a message accepted for a parked target wakes it (`kin_wake`).|A mailbox that queues and never delivers.|
|O7|`mail_return_reason_true`|A message is returned exactly when it was accepted, not yet delivered, and its target ended, was deleted or refused it; the reason it carries is that one.|Silent success on a dead agent; every return labelled "ended"; a message returned while its target could take it.|
|O8|`mail_delivered_once`|No id is delivered twice, for any order of redeliveries and crashes.|At-least-once retry without the id check.|
|O8|`mail_pair_fifo`|For one sender and one target, delivery order is acceptance order, and a report is delivered after every message its sender had accepted before it.|A report on a fast path past queued messages.|
|O9|`waitfor_edges_exact`|An accepted wait adds exactly its edge to the relation, and an ended wait removes exactly its edge.|An add that keeps the graph unchanged, so nothing is ever a cycle.|
|O9|`waitfor_stays_acyclic`|In every reachable state the wait-for relation has no cycle; a wait that would close one is refused, and the path it returns is a cycle of the relation with that wait added.|A check of direct cycles only (a waits b, b waits a) missing three agents.|
|O9|`waitfor_message_ends_wait`|A message delivered to an agent that waits on its sender ends that wait with the message.|A question queued behind the wait it could answer.|
|O9|`sched_counts_all_or_none`|No unit counts under one limit of its path while it waits for room under another.|Take the tree's slot, then wait for the provider's.|
|O9|`wait_lends_slots`|A unit blocked in a wait counts under no limit; when its wait ends it is admitted before every unit of its tree and class that arrived after it began to wait.|A parent that holds its tree's last slot while it waits on a child queued for that slot.|
|O10|`wait_has_exit`|A wait is accepted only with a running target or a deadline; with neither it is refused (carries `wait_any` S2 to agents and loops).|A wait on a child that already reported.|
|O10|`wait_ends_with_target`|In the step the last thing a wait watches ends or dies, the wait ends with that reason.|A wait on a crashed child that never returns.|
|O10|`stall_ends_only_running`|A running unit that records no act for its stall bound is ended and stops counting; no unit is ended as stalled while it waits in a queue or in a wait.|A stalled child that keeps its slot; a queued unit killed for making no progress.|
|O11|`stop_exact`|A stop ends exactly the units of the stopped agent's subtree; outside it the only changes are admissions into the freed room, returns of its undelivered messages, and ends of waits on its agents.|A stop that aborts siblings spawned in the same batch.|
|O11|`stop_is_bounded`|After a stop, within as many steps as the subtree has units, none of them runs or counts.|A stop that waits for each child's next model reply.|
|O12|`control_answers_in_step`|In every reachable state, full queues included, a status request is answered in its step with that state's limits, counts and waiting units, and a stop has the effect of `stop_exact`; neither changes a count or a queue length by itself.|Status sent through the saturated worker queue; a constant "busy".|
|O13|`stream_tiles`|What a reader receives, events and gaps together, covers every sequence number exactly once, in order.|A drop with no marker; a gap that overlaps delivered events.|
|O13|`stream_no_gap_within_ring`|A reader that never lags by more than the ring holds receives every event and no gap.|Gaps for everyone as soon as one reader lags.|
|O13|`stream_readers_independent`|A reader's frames are the same for every behaviour of the other readers, and the writer's step is the same for every reader state.|A shared cursor; a full reader buffer that blocks the publish.|
|O13|`stream_gap_fill_exact`|Reading a gap back from the record gives exactly the events of its range.|A resync that restarts from the present.|
|O14|`sched_rebuild_same`|The state rebuilt from the durable facts after a crash equals the state before it with the dead holders ended and the admissions that follow made: the same queues in the same order.|A rebuild in directory order.|
|O14|`sched_status_exact`|For each waiting unit, the limit the status names has no room, the place is the unit's place in the order of O4 and O5, and the holders are exactly the units that count under that limit.|A status that names a limit with room, or yesterday's place.|

Already proven and reused: the admission laws (as the provider scope), R1,
R3, A3 (`kin_wake`, `kin_admit_iff`), the child's report laws, D3, D4, the
wait laws.

## 5. Core sketch

`bend/sched.bend` (a stepper), `bend/mailbox.bend` (a stepper),
`bend/waitfor.bend` (plain calls), `bend/stream.bend` (a stepper):

```
type Scope:  Daemon | Tree{root} | Provider{id}
type Unit:   Unit{id, tree, class, needs: List<Scope>}
type Op:     Arrive{batch} | End{id} | Cancel{id} | Crash{id} | Block{id} | Unblock{id} | Stop{agent} | Status | Tick
sched.step(state, op) -> (state, List<Out>)       # Admit{id} | Queue{id} | Refuse{id, queue, limit} | Preempt{id} | State{..}

type Mail:   Mail{id, from, to, seq}
mailbox.step(state, ev) -> (state, List<Out>)     # Accept Hold Deliver Return{reason} Wake; ev: Send Busy Idle End Delete Crash

waitfor.add(graph, a, b) -> Ok{graph} | Cycle{path}
waitfor.end(graph, a, b) -> graph
stream.step(ring, ev) -> (ring, List<Frame>)      # Event{seq} | Gap{from, to}; one cursor per reader
```

The scheduler is the admission controller made hierarchical: the provider
scope keeps today's rules and laws; a tree scope and a daemon scope sit
above it. Among the eligible units it picks by one order: the oldest
eligible background unit when its turn has come (O5), else interactive
units by weighted round robin over trees, else background units the same
way; FIFO inside a tree among units that need the same limits. A unit is
counted under all its limits in one step or none, and a blocked unit is
not counted (O9). The family cap, the workflow semaphore and the query cap
become limits of this one scheduler, so one law covers them. The mailbox
carries kin's rule, the child's report and the session inbox under one
bound and one id space; exactly-once delivery is shared with the
exactly-once pillar (one id, one dedup rule). Rust keeps IO only:
processes, sockets, timers; the constants of `backpressure.rs` become the
bounds the core is opened with.

Shared with other pillars: a budget (budgets pillar) refuses before a limit
does, and the refusal order is one law; a loop iteration (loop pillar) is a
unit; a gap is filled from the record (`spec/record/SPEC.md`); limits per
principal come from the capability set (`spec/security/SPEC.md`).

## 6. Surface

- Daemon and SDK: `sched_status {scope}` (limits, running, queued, for each
  waiting unit its reason and place), `sched_set_limit`, events `unit_queued`,
  `unit_admitted`, `unit_refused {limit}`, `message_returned {id, reason}`,
  `stream_gap {from, to}`; error codes `limit_full`, `queue_full`,
  `wait_cycle`; settings `limits.daemon.agents`, `limits.tree.agents`,
  `limits.tree.weight`, the queue bounds.
- CLI and TUI: `eukhe ps` (every tree, what runs, what waits and why),
  `eukhe limits`, the agents view shows "waiting: tree limit 8/8, place 3".

## 7. Tests (with the implementation)

One per requirement, through the entries. Crash and restart: kill a worker
that holds slots (they free), kill the daemon with queues full (order kept,
nothing twice), kill a target between accept and deliver (delivered once
after restart). Load: a thousand queued units over ten trees, each tree's
first unit starts within the bound; a flooding tree does not delay another
tree's interactive turn. Real `claude-haiku-5-5` runs: two roots, one
spawning to its cap, the other still answers within its usual time; a
parent that waits on a child while the child asks it a question gets the
question, not a hang.

## 8. Trust

Proven: admission, fairness, bounds, conservation, acyclic waits, over the
steppers for every order of events. Trusted: the operating system's process
and socket behaviour, timers. Tested, not proven: that Rust sends every
event to the stepper (a missed release shows as a leak in the load tests),
memory per agent, wall-clock bounds.

## 9. Open questions for the user

1. Who is the tenant? The root session (assumed), the user or client that
   owns several roots, or a loop? Do weights come from budgets?
2. Interactive and background: strict priority as today (background may
   wait without bound on a capped provider), or a bounded wait for
   background (assumed in O5)? What bound?
3. At a full queue: refuse at once (today: `worker_overloaded`,
   `providerMaxQueued`) or hold the sender? Assumed: units wait up to the
   bound and are then refused; client commands are refused at their
   in-flight bound; agent-to-agent messages hold the sender. Agree?
4. Daemon-wide limits: how many running agents per machine by default? A
   unit blocked in a wait does not count (O9), so the live processes can
   exceed the limit: should a second, hard cap on live agents refuse a
   spawn outright (assumed: yes, a refusal, never a queue)?
5. A wait that would close a cycle: refuse it with the cycle (assumed), or
   allow it and break it after a timeout?
6. Who may message whom? Parent and children only (today), or also
   siblings and a broadcast? It changes the wait-for graph and the mailbox
   bounds.
7. Scale target: hundreds, thousands, or more agents on one daemon? One
   machine only (assumed), or several daemons sharing limits?
8. A reader that lags: drop, mark the gap and let it read back (assumed),
   or disconnect it?
9. May an interactive unit preempt a running background agent (pause it at
   its next boundary), beyond today's preemption of compactor requests?
10. Should the provider's admission laws be kept as they are under the new
    scheduler (assumed), or restated as one instance of it?
