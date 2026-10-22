# orphan: the model of a worker whose supervisor is lost (docs/daemon.md
# D1). It runs compiled as the Rust rule: `work_gate::orphan_decision`
# (crates/eukhe-daemon/src) calls `exit_due.at` and `orphan_exit` through
# bend/ffi_orphan.bend. The event machine below (`step`, `run`) is the
# law `orphan_never_aborts_resumable`'s history.
#
# Any events, in any order: a run starts or ends, an input is queued or
# drained, a compaction starts or ends, the supervisor stays unreachable
# for g more ms, the supervisor answers again. After each event the
# worker checks the exit: with no work it exits after the window, with
# work after two windows. Its exit closes the session when it holds no
# work, and hands the work over (records it busy, aborts nothing) when it
# holds work.

import Base

type Ev is Data:
  RunStart{}
  RunEnd{}
  Queue{}
  Drain{}
  CompactStart{}
  CompactEnd{}
  Gone{g: Nat}
  Back{}

type Work is Data:
  Idle{}
  Ongoing{}

type Exit is Data:
  Shut{}
  Handover{}

# what an exit did: how, the work at the exit, the busy flag it recorded,
# whether it aborted a run
type Out is Data:
  Out{exit: Exit, work: Work, busy: Bool, aborted: Bool}

# a live worker: a run, the queued inputs, a compaction, the ms the
# supervisor has been unreachable
type W is Data:
  W{run: Bool, queued: Nat, compacting: Bool, absent: Nat}

type St is Data:
  Live{w: W}
  Exited{d: Out}

def W.empty() -> W:
  W{False{}, 0n, False{}, 0n}

def work.put(b: Bool) -> Work:
  match b:
    case True{}:
      Ongoing{}
    case False{}:
      Idle{}

def queued_any(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}

# the work of a worker: a run, a compaction, or a queued input
def W.work(w: W) -> Work:
  match w:
    case W{r, q, c, a}:
      work.put(Bool.or(r, Bool.or(c, queued_any(q))))

# whether the worker exits after `absent` ms with the window: without
# work once the window passed, with work once two windows passed
# (`window <= absent - window`: no sum that could pass the Nat range)
def exit_due(+window: Nat, +absent: Nat, work: Work) -> Bool:
  match work:
    case Idle{}:
      Nat.is_le(window, absent)
    case Ongoing{}:
      Nat.is_le(window, Nat.sub(absent, window))

# the decision the Rust makes: `None` is a window past the wire's Nat
# range (10^14 - 1 ms, about 3170 years; Rust saturates the env window
# there), which never expires; the absence saturates at the same cap
def exit_due.at(window: Maybe<&2, Nat>, +absent: Nat, work: Work) -> Bool:
  match window:
    case None{}:
      False{}
    case Some{w}:
      exit_due(w, absent, work)

# how a worker with this work exits: it shuts the session, or it hands
# the work over
def orphan_exit(work: Work) -> Exit:
  match work:
    case Idle{}:
      Shut{}
    case Ongoing{}:
      Handover{}

def work.is_ongoing(work: Work) -> Bool:
  match work:
    case Idle{}:
      False{}
    case Ongoing{}:
      True{}

# what an exit with this work does: a handover records the session busy
# and aborts nothing; a shut records it idle and aborts what runs
def exit.done(e: Exit, +work: Work) -> Out:
  match e:
    case Shut{}:
      Out{Shut{}, work, False{}, work.is_ongoing(work)}
    case Handover{}:
      Out{Handover{}, work, True{}, False{}}

def check.put(due: Bool, +w: W) -> St:
  match due:
    case True{}:
      Exited{exit.done(orphan_exit(W.work(w)), W.work(w))}
    case False{}:
      Live{w}

# the exit check after an event
def check(+window: Nat, +w: W) -> St:
  match w:
    case W{r, q, c, +a}:
      check.put(exit_due(window, a, W.work(W{r, q, c, a})), W{r, q, c, a})

def dec(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def apply(w: W, e: Ev) -> W:
  match w:
    case W{r, q, c, a}:
      match e:
        case RunStart{}:
          W{True{}, q, c, a}
        case RunEnd{}:
          W{False{}, q, c, a}
        case Queue{}:
          W{r, 1n+q, c, a}
        case Drain{}:
          W{r, dec(q), c, a}
        case CompactStart{}:
          W{r, q, True{}, a}
        case CompactEnd{}:
          W{r, q, False{}, a}
        case Gone{g}:
          W{r, q, c, Nat.add(g, a)}
        case Back{}:
          W{r, q, c, 0n}

def step(+window: Nat, s: St, e: Ev) -> St:
  match s:
    case Live{w}:
      check(window, apply(w, e))
    case Exited{d}:
      Exited{d}

def go(+window: Nat, evs: List<&2, Ev>, s: St) -> St:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      go(window, rest, step(window, s, e))

def run(+window: Nat, evs: List<&2, Ev>) -> St:
  go(window, evs, Live{W.empty()})

# an exit aborted nothing, and recorded the session busy exactly when it
# held work
def Sound(s: St) -> Type:
  match s:
    case Live{w}:
      Unit
    case Exited{d}:
      match d:
        case Out{e, work, busy, aborted}:
          ({aborted == False{} : Bool} & {busy == work.is_ongoing(work) : Bool})
