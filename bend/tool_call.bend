# tool_call: the model of one tool call's journal (call 1-3) and of its
# effect gate (speculation, then effect). The Harness
# (crates/eukhe-durable/src/harness/tool.rs and
# tool/invocation.rs) runs the journal as the stepper
# bend/ffi_tool_call.bend: it opens the call where it journals the call's
# start, sends every report the tool makes and the end of its execute in
# the order they come (from any thread), and does what each reply says.
# It keeps what the tool reported (output, diagnostics, usage, details);
# the model decides only what is stored and what is journaled when. The
# gate (`gate`, the call `ffi` of the same entry) says whether a call's
# effect may run, at each handler of its tool task.

import Base

# What the Harness sees of a running call, in arrival order
type Ev is Data:
  Report{}                         # the tool reports: output, a diagnostic, usage, details, a read of its output, a nested call
  End{threw: Bool, aborted: Bool}  # the tool's execute returned (threw: with an error), its signal aborted or not

# How a call ends
type How is Data:
  Finished{}   # with the tool's result
  Failed{}     # with the tool's error: it threw, its signal not aborted
  Cancelled{}  # aborted: the abort handler settles it from the progress board

# What the Harness does with an event
type Act is Data:
  Keep{}           # store the report
  Refuse{}         # refuse the report: the call has ended
  Settle{how: How} # the call ended: journal its settle, as how
  Late{}           # an end after the end: nothing

# The record an open journals
type Rec is Data:
  Began{}    # a first attempt: the slot goes running
  Cleared{}  # a rerun after a restart: the slot's progress is cleared

# A call: taking reports, or ended
type C is Data:
  Taking{}
  Ended{}

# how an execute that threw or not, its signal aborted or not, ends the
# call (`ToolEnding`)
def how(threw: Bool, aborted: Bool) -> How:
  match threw:
    case False{}:
      Finished{}
    case True{}:
      match aborted:
        case True{}:
          Cancelled{}
        case False{}:
          Failed{}

# a call opens taking reports; first says a first attempt
def open(first: Bool) -> C & Rec:
  match first:
    case True{}:
      (Taking{}, Began{})
    case False{}:
      (Taking{}, Cleared{})

# one event: the call after it, and what the Harness does
def step(c: C, e: Ev) -> C & Act:
  match c:
    case Taking{}:
      match e:
        case Report{}:
          (Taking{}, Keep{})
        case End{t, a}:
          (Ended{}, Settle{how(t, a)})
    case Ended{}:
      match e:
        case Report{}:
          (Ended{}, Refuse{})
        case End{t, a}:
          (Ended{}, Late{})

# The effect gate
# ---------------
# A tool's effects run only once the assistant entry that made the call is
# durable. The streamed reply is speculation: nothing runs from it. The
# Harness creates a call's tool task in the commit that appends its
# assistant entry (harness/generation/round.rs), and the task asks the
# gate at each of its handlers (harness/tool.rs): the call phase (a first
# run, or a run again after a restart before the intent was recorded),
# the execute phase (a restart after the intent), and abort. found: a
# committed entry holds the call (a nested call's task input holds its
# call, so it is always found).

# A tool's replay policy (`ToolReplay`; a tool that names none is unsafe)
type Replay is Data:
  Safe{}    # an interrupted run may run again
  Unsafe{}  # it may have changed state: never run it twice

# The called tool as the task resolves it now
type Now is Data:
  Gone{}              # no longer offered
  Offered{r: Replay}  # offered, with its replay policy

# What a tool task asks before anything of its call happens
type Gate is Data:
  Enter{found: Bool, tool: Now}                    # the call phase starts
  Recover{found: Bool, stored: Replay, tool: Now}  # the execute phase: a restart after the intent (stored: the policy the intent recorded)
  Stop{found: Bool, restart: Bool, intent: Bool}   # the abort handler (restart: abandoned by a restart; intent: recorded)

# What the task does
type Go is Data:
  Run{}          # record the intent, then execute
  Missing{}      # no committed entry holds the call: nothing runs, nothing settles
  Unavailable{}  # settle `tool_unavailable`: nothing ran
  Rerun{}        # execute again
  Interrupted{}  # settle `interrupted`: it may have partially run; no execute
  Aborted{}      # settle `aborted`
  Abandoned{}    # settle `abandoned`: it never started

# a found call starts when its tool is offered
def gate.enter(tool: Now) -> Go:
  match tool:
    case Gone{}:
      Unavailable{}
    case Offered{r}:
      Run{}

# the tool offered now reruns only when it is safe
def gate.now(tool: Now) -> Go:
  match tool:
    case Gone{}:
      Interrupted{}
    case Offered{r}:
      match r:
        case Safe{}:
          Rerun{}
        case Unsafe{}:
          Interrupted{}

# a recorded intent reruns only when the stored and the current policy
# are both safe
def gate.recover(stored: Replay, tool: Now) -> Go:
  match stored:
    case Safe{}:
      gate.now(tool)
    case Unsafe{}:
      Interrupted{}

# an abort settles aborted; one by a restart says whether the call may
# have run
def gate.stop(restart: Bool, intent: Bool) -> Go:
  match restart:
    case False{}:
      Aborted{}
    case True{}:
      match intent:
        case True{}:
          Interrupted{}
        case False{}:
          Abandoned{}

# the gate: a call no committed entry holds does nothing
def gate(q: Gate) -> Go:
  match q:
    case Enter{found, tool}:
      match found:
        case True{}:
          gate.enter(tool)
        case False{}:
          Missing{}
    case Recover{found, stored, tool}:
      match found:
        case True{}:
          gate.recover(stored, tool)
        case False{}:
          Missing{}
    case Stop{found, restart, intent}:
      match found:
        case True{}:
          gate.stop(restart, intent)
        case False{}:
          Missing{}
