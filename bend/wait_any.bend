# wait_any: the model of `jobs.wait`, the agent's one blocking wait on its
# own work (spec/durable/wait_any.bend; laws/wait_any.bend). Run as the
# compiled core by bend/ffi_wait_any.bend (eukhe-bend rules/wait_any.rs;
# asked by eukhe-core durable/rlm/wait.rs and durable/jobs).
#
# A wait watches targets, each running, settled with a result no one
# delivered yet (ready), or settled and delivered (gone). Each poll the
# host sends what it finds: the targets, whether the user's cancel fired,
# whether the cap passed. The wait takes the first settled target; with
# nothing running and nothing ready it refuses (nothing to wait for). A
# named wait (the caller named its targets) takes a gone target too: the
# caller asked for that one. A settled target wins over the cancel and the
# cap, the cancel over the cap.
#
# A job's result goes one way: to a wait watching it, or to the session's
# notice (the job-settled wake). It goes to the notice only when no wait
# watches it and the session has a wake path; else it stays held for a
# wait. A wait that ends without taking a held result hands it on by the
# same rule. So each result is delivered at most once.

import Base

# A target as the host finds it
type Tgt is Data:
  Runs{}
  Unread{}
  Read{}

# What one poll of a wait decides
type Pick is Data:
  Waits{}       # keep waiting
  Takes{i: Nat} # the wait ends with target i
  NoWork{}    # refused: nothing to wait for
  Capped{}    # the cap passed, nothing settled
  Stopped{}  # the user's cancel

# Where a settled job's result goes
type Route is Data:
  ToWaiter{}   # held for a wait
  ToNotice{}   # the session's job-settled notice

# The poll
# --------

# t counts as settled: ready always, gone for a named wait
def settled(+named: Bool, t: Tgt) -> Bool:
  match t:
    case Runs{}:
      False{}
    case Unread{}:
      True{}
    case Read{}:
      named

def first.pick(here: Bool, i: Nat, later: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match here:
    case True{}:
      Some{i}
    case False{}:
      later

# the index (from i) of the first settled target of ts
def first(ts: List<&2, Tgt>, +named: Bool, +i: Nat) -> Maybe<&2, Nat>:
  match ts:
    case Nil{}:
      None{}
    case Con{t, rest}:
      first.pick(settled(named, t), i, first(rest, named, 1n+i))

# some target of ts still runs
def live(ts: List<&2, Tgt>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{t, rest}:
      match t:
        case Runs{}:
          True{}
        case Unread{}:
          live(rest)
        case Read{}:
          live(rest)

def poll.open(cancel: Bool, late: Bool) -> Pick:
  match cancel:
    case True{}:
      Stopped{}
    case False{}:
      match late:
        case True{}:
          Capped{}
        case False{}:
          Waits{}

def poll.none(running: Bool, cancel: Bool, late: Bool) -> Pick:
  match running:
    case True{}:
      poll.open(cancel, late)
    case False{}:
      NoWork{}

def poll.found(f: Maybe<&2, Nat>, running: Bool, cancel: Bool, late: Bool) -> Pick:
  match f:
    case Some{i}:
      Takes{i}
    case None{}:
      poll.none(running, cancel, late)

# one poll: named wait or not, the cancel fired, the cap passed, the targets
def poll(+named: Bool, cancel: Bool, late: Bool, +ts: List<&2, Tgt>) -> Pick:
  poll.found(first(ts, named, 0n), live(ts), cancel, late)

# The route of a result
# ---------------------

# a settled (or still held) result: watched by a wait, the session has a
# wake path
def route(watched: Bool, wake: Bool) -> Route:
  match watched:
    case True{}:
      ToWaiter{}
    case False{}:
      match wake:
        case True{}:
          ToNotice{}
        case False{}:
          ToWaiter{}

# The cap
# -------

# the longest wait, in seconds: 30 minutes
def cap() -> Nat:
  1800n

# the wait's length in seconds: what the caller asked (None: the cap), at
# most the cap
def timeout(asked: Maybe<&2, Nat>) -> Nat:
  match asked:
    case None{}:
      cap()
    case Some{t}:
      Nat.min(t, cap())

# One job's delivery
# ------------------
# The life of one job's result as the host drives it: waits start and stop
# watching it, the job settles once, a wait takes it. `wake` is whether the
# session has a wake path. Each step answers how many deliveries it made.

type Ev is Data:
  Watch{}
  Unwatch{}
  Settles{}
  Taken{}

type Phase is Data:
  Live{}  # the job runs
  Kept{}  # settled, held for a wait
  Sent{}  # settled, delivered

type D is Data:
  D{watchers: Nat, phase: Phase}

# a step's answer: the state after it, the deliveries it made
type Out is Data:
  Out{d: D, k: Nat}

def Out.d(o: Out) -> D:
  match o:
    case Out{d, k}:
      d

def Out.k(o: Out) -> Nat:
  match o:
    case Out{d, k}:
      k

def unwatch.left(w: Nat) -> Nat:
  match w:
    case 0n:
      0n
    case 1n+p:
      p

def watched(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}

# a held result after its last watcher left (or a settle) goes where route says
def deliver(r: Route, +w: Nat) -> Out:
  match r:
    case ToWaiter{}:
      Out{D{w, Kept{}}, 0n}
    case ToNotice{}:
      Out{D{w, Sent{}}, 1n}

def step.unwatch(+wake: Bool, +w: Nat, p: Phase) -> Out:
  match p:
    case Live{}:
      Out{D{w, Live{}}, 0n}
    case Kept{}:
      deliver(route(watched(w), wake), w)
    case Sent{}:
      Out{D{w, Sent{}}, 0n}

def step.settle(+wake: Bool, +w: Nat, p: Phase) -> Out:
  match p:
    case Live{}:
      deliver(route(watched(w), wake), w)
    case Kept{}:
      Out{D{w, Kept{}}, 0n}
    case Sent{}:
      Out{D{w, Sent{}}, 0n}

def step.take(+w: Nat, p: Phase) -> Out:
  match p:
    case Live{}:
      Out{D{w, Live{}}, 0n}
    case Kept{}:
      Out{D{w, Sent{}}, 1n}
    case Sent{}:
      Out{D{w, Sent{}}, 0n}

# one event: the job's delivery state after it, and the deliveries it made
def step(+wake: Bool, d: D, e: Ev) -> Out:
  match d:
    case D{w, p}:
      match e:
        case Watch{}:
          Out{D{1n+w, p}, 0n}
        case Unwatch{}:
          step.unwatch(wake, unwatch.left(w), p)
        case Settles{}:
          step.settle(wake, w, p)
        case Taken{}:
          step.take(w, p)

# every delivery the events es make from d
def deliveries(es: List<&2, Ev>, +wake: Bool, d: D) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, rest}:
      +r = step(wake, d, e)
      Nat.add(Out.k(r), deliveries(rest, wake, Out.d(r)))

# a job before any event: no watcher, running
def fresh() -> D:
  D{0n, Live{}}
