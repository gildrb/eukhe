# harness (spec): speculation, then effect (area tool_call), restated
# without the rules of bend/tool_call.bend: the gate a tool task asks at
# each of its handlers, and the world of one model-issued call (its
# streamed reply, the commit of its assistant entry and tool task, the
# scheduler's runs of the task, crashes, aborts) the laws run the shipped
# gate in. The laws of area tool_call (laws/tool_call.bend) state that the
# gate refines it and what the world keeps. A spec: the shipped code never
# calls it.
#
# E1: a call runs (its intent recorded, then its execute) only when a
#     committed assistant entry holds it and its tool is offered; found
#     but no longer offered, it settles `tool_unavailable` and nothing
#     runs.
# E2: after a restart that found its intent recorded, a call runs again
#     only when the policy its intent recorded and the policy of the tool
#     offered now are both safe; else it settles `interrupted` (it may
#     have partially run) and does not run.
# E3: an abort settles `aborted`; one by a restart settles `interrupted`
#     when the intent was recorded, else `abandoned` (it never started).
# E4: a call no committed entry holds does nothing at all: no run, no
#     settle.
# E5 (the world): the streamed reply is speculation; the assistant entry
#     and the call's tool task land in one commit; the scheduler runs the
#     task's current phase (never a running one, never a settled one);
#     the end of a running execute settles the call; a crash ends what
#     ran in memory and keeps every commit.

import Base
import ../../bend/tool_call.bend as Tc

# The gate (E1-E4)
# ----------------

# the answer E1-E4 ask of every question, as one table
def gate_spec(q: Tc.Gate) -> Tc.Go:
  match q:
    case Tc.Enter{found, tool}:
      match found tool:
        case True{} Tc.Offered{r}:
          Tc.Run{}
        case True{} Tc.Gone{}:
          Tc.Unavailable{}
        case False{} Tc.Offered{r}:
          Tc.Missing{}
        case False{} Tc.Gone{}:
          Tc.Missing{}
    case Tc.Recover{found, stored, tool}:
      match found stored tool:
        case True{} Tc.Safe{} Tc.Offered{Tc.Safe{}}:
          Tc.Rerun{}
        case True{} Tc.Safe{} Tc.Offered{Tc.Unsafe{}}:
          Tc.Interrupted{}
        case True{} Tc.Safe{} Tc.Gone{}:
          Tc.Interrupted{}
        case True{} Tc.Unsafe{} Tc.Offered{p}:
          Tc.Interrupted{}
        case True{} Tc.Unsafe{} Tc.Gone{}:
          Tc.Interrupted{}
        case False{} s t:
          Tc.Missing{}
    case Tc.Stop{found, restart, intent}:
      match found restart intent:
        case True{} False{} i:
          Tc.Aborted{}
        case True{} True{} True{}:
          Tc.Interrupted{}
        case True{} True{} False{}:
          Tc.Abandoned{}
        case False{} x i:
          Tc.Missing{}

# The world of one call (E5)
# --------------------------

# Where the call's tool task is
type Phase is Data:
  NoTask{}                       # none: the call is speculation (streamed, not committed)
  AtCall{}                       # at its call checkpoint: no intent recorded
  AtExecute{q: Tc.Replay}        # its intent recorded, with policy q
  Settled{q: Maybe<&2, Tc.Replay>}  # its result settled (q: the policy its intent recorded, if any)

# The world: whether the assistant entry is committed, the task's phase,
# whether its execute runs in memory now, how many times the call's
# effect ran, how many times it settled, and how many of the runs came
# while no committed entry held the call
type World is Data:
  Wd{committed: Bool, phase: Phase, running: Bool, effects: Nat, settles: Nat, early: Nat}

# What happens to the call
type Ev is Data:
  Delta{}               # a chunk of the streamed reply (the call's arguments included)
  Commit{}              # the assistant entry and the call's tool task land, in one commit
  Start{tool: Tc.Now}   # the scheduler runs the task's current phase; the tool resolves as tool
  Finish{}              # the running execute returns: its result settles the call
  Crash{}               # the process dies: what ran in memory is gone, every commit stays
  Abort{restart: Bool}  # the abort handler runs (restart: abandoned by a restart)

# before anything: nothing committed, no task
def w0() -> World:
  Wd{False{}, NoTask{}, False{}, 0n, 0n, 0n}

# Terms
# -----

def early(w: World) -> Nat:
  match w:
    case Wd{c, ph, r, n, s, x}:
      x

def effects(w: World) -> Nat:
  match w:
    case Wd{c, ph, r, n, s, x}:
      n

def settles(w: World) -> Nat:
  match w:
    case Wd{c, ph, r, n, s, x}:
      s

# the intent this phase recorded, if any
def intent_of(ph: Phase) -> Maybe<&2, Tc.Replay>:
  match ph:
    case NoTask{}:
      None{}
    case AtCall{}:
      None{}
    case AtExecute{q}:
      Some{q}
    case Settled{q}:
      q

# the call's intent recorded a safe policy
def safe_intent(w: World) -> Bool:
  match w:
    case Wd{c, ph, r, n, s, x}:
      match ph:
        case NoTask{}:
          False{}
        case AtCall{}:
          False{}
        case AtExecute{q}:
          match q:
            case Tc.Safe{}:
              True{}
            case Tc.Unsafe{}:
              False{}
        case Settled{q}:
          match q:
            case None{}:
              False{}
            case Some{p}:
              match p:
                case Tc.Safe{}:
                  True{}
                case Tc.Unsafe{}:
                  False{}

# the policy an intent records for the tool resolved as tool (a tool that
# names none is unsafe)
def policy(tool: Tc.Now) -> Tc.Replay:
  match tool:
    case Tc.Gone{}:
      Tc.Unsafe{}
    case Tc.Offered{r}:
      r

# x, plus one when the entry is not committed (a run counted early)
def early_add(c: Bool, x: Nat) -> Nat:
  match c:
    case True{}:
      x
    case False{}:
      1n+x

# es holds a commit
def commits(es: List<&2, Ev>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Delta{}:
          commits(rest)
        case Commit{}:
          True{}
        case Start{t}:
          commits(rest)
        case Finish{}:
          commits(rest)
        case Crash{}:
          commits(rest)
        case Abort{x}:
          commits(rest)
