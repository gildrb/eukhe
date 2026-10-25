# eukhe: the laws of area throttle

import Base
import ../bend/throttle.bend as Th
import ../bend/ffi_throttle.bend as FTh
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1): the throttle of one streamed request's partials
# (bend/throttle.bend, the port of eukhe-durable
# harness/generation/stream.rs `Throttle`, `StopOnDrop`). Each law is an
# open claim about Th.step; PROOF.bend proves them (as Throttle.<law>)
# with the lemmas of proof/throttle/.
#
# The host steps the throttle with each event of the request and does the
# actions the step answers, in order; it keeps the timer, the commit in
# flight and the pending partial's value.
#
# R1: a partial with content, before the stop, becomes the pending one
#     (the host keeps it) and starts the timer unless a timer runs or a
#     commit is in flight; a partial with no content changes nothing.
# R2: the timer firing ends the timer and takes the pending partial; it
#     starts a commit of it unless the request stopped; with no partial
#     pending it does nothing. At most one commit is in flight: a commit
#     starts only when none is.
# R3: a commit settling ends the commit in flight; with a partial pending
#     and no stop the timer starts again.
# R4: the stop aborts the timer and awaits the commit in flight; a
#     dropped request aborts the timer. After either nothing commits and
#     no timer starts.
# R5: progress: a partial pending with no stop always has a timer running
#     or a commit in flight, never both, so it is committed eventually.
# A timer that fires when none runs (one aborted as it woke) and a commit
# that settles when none is in flight change nothing.

# Terms
# -----

def when(b: Bool, a: Th.Act) -> List<&2, Th.Act>:
  match b:
    case True{}:
      [a]
    case False{}:
      []

# R1-R4 per event, as formulas over the flags: the throttle after the
# event and the host's actions in order
def step_spec(g: Th.Gate, e: Th.Ev) -> Th.Moved:
  match g:
    case Th.Gate{+p, +t, +f, +s}:
      match e:
        case Th.Part{shows}:
          +live = Bool.and(Bool.not(s), shows)
          Th.Moved{Th.Gate{Bool.or(p, live), Bool.or(t, Bool.and(live, Bool.not(f))), f, s}, List.append(&2, Th.Act, when(live, Th.Keep{}), when(Bool.and(live, Bool.not(Bool.or(t, f))), Th.Arm{}))}
        case Th.Fire{}:
          +go = Bool.and(t, Bool.and(p, Bool.not(s)))
          Th.Moved{Th.Gate{Bool.and(p, Bool.or(Bool.not(t), Bool.and(Bool.not(s), f))), False{}, Bool.or(f, go), s}, when(Bool.and(go, Bool.not(f)), Th.Commit{})}
        case Th.Settle{}:
          +go = Bool.and(f, Bool.and(p, Bool.not(s)))
          Th.Moved{Th.Gate{p, Bool.or(t, go), False{}, s}, when(Bool.and(go, Bool.not(t)), Th.Arm{})}
        case Th.Finish{}:
          Th.Moved{Th.Gate{p, False{}, False{}, True{}}, List.append(&2, Th.Act, when(t, Th.Abort{}), when(f, Th.Await{}))}
        case Th.Quit{}:
          Th.Moved{Th.Gate{p, False{}, f, True{}}, when(t, Th.Abort{})}

def pending(g: Th.Gate) -> Bool:
  match g:
    case Th.Gate{p, t, f, s}:
      p

def timer(g: Th.Gate) -> Bool:
  match g:
    case Th.Gate{p, t, f, s}:
      t

def flight(g: Th.Gate) -> Bool:
  match g:
    case Th.Gate{p, t, f, s}:
      f

def stopped(g: Th.Gate) -> Bool:
  match g:
    case Th.Gate{p, t, f, s}:
      s

# how many commits the actions start
def commits(acts: List<&2, Th.Act>) -> Nat:
  match acts:
    case Nil{}:
      0n
    case a <> t:
      match a:
        case Th.Keep{}:
          commits(t)
        case Th.Arm{}:
          commits(t)
        case Th.Commit{}:
          1n+commits(t)
        case Th.Abort{}:
          commits(t)
        case Th.Await{}:
          commits(t)

# the actions start a commit or a timer
def moves(acts: List<&2, Th.Act>) -> Bool:
  match acts:
    case Nil{}:
      False{}
    case a <> t:
      match a:
        case Th.Keep{}:
          moves(t)
        case Th.Arm{}:
          True{}
        case Th.Commit{}:
          True{}
        case Th.Abort{}:
          moves(t)
        case Th.Await{}:
          moves(t)

def one_commit.n(n: Nat, f0: Bool, f1: Bool) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+k:
      match k:
        case 0n:
          Bool.and(Bool.not(f0), f1)
        case 1n+j:
          False{}

# R2: the step starts no commit, or one commit when none was in flight,
# and then one is
def one_commit(+g: Th.Gate, m: Th.Moved) -> Bool:
  match m:
    case Th.Moved{g2, acts}:
      one_commit.n(commits(acts), flight(g), flight(g2))

def takes.n(n: Nat, p0: Bool, p1: Bool) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+k:
      Bool.and(p0, Bool.not(p1))

# R2: a step that starts a commit had a partial pending and takes it
def takes(+g: Th.Gate, m: Th.Moved) -> Bool:
  match m:
    case Th.Moved{g2, acts}:
      takes.n(commits(acts), pending(g), pending(g2))

# R4: no commit and no timer starts, and the throttle stays stopped
def quiet(m: Th.Moved) -> Bool:
  match m:
    case Th.Moved{g2, acts}:
      Bool.and(Bool.not(moves(acts)), stopped(g2))

# R4: a stop: quiet, and no timer runs
def ends(m: Th.Moved) -> Bool:
  match m:
    case Th.Moved{+g2, acts}:
      Bool.and(Bool.and(Bool.not(moves(acts)), stopped(g2)), Bool.not(timer(g2)))

# R5: never a timer and a commit at once; a partial pending with no stop
# has a timer or a commit
def good(g: Th.Gate) -> Bool:
  match g:
    case Th.Gate{p, +t, +f, s}:
      Bool.and(Bool.not(Bool.and(t, f)), Bool.or(s, Bool.or(Bool.not(p), Bool.or(t, f))))

def after(m: Th.Moved) -> Th.Gate:
  match m:
    case Th.Moved{g2, acts}:
      g2

def actions(m: Th.Moved) -> List<&2, Th.Act>:
  match m:
    case Th.Moved{g2, acts}:
      acts

# R5: the event wakes a pending partial with no stop: the running timer
# fires, or the commit in flight settles
def wakes(g: Th.Gate, e: Th.Ev) -> Bool:
  match g:
    case Th.Gate{p, t, f, s}:
      match e:
        case Th.Part{shows}:
          False{}
        case Th.Fire{}:
          Bool.and(t, Bool.and(p, Bool.not(s)))
        case Th.Settle{}:
          Bool.and(f, Bool.and(p, Bool.not(s)))
        case Th.Finish{}:
          False{}
        case Th.Quit{}:
          False{}

# the actions of the throttle driven over the events es from g, in order
def drive(es: List<&2, Th.Ev>, g: Th.Gate) -> List<&2, List<&2, Th.Act>>:
  match es:
    case Nil{}:
      []
    case e <> t:
      +m = Th.step(g, e)
      actions(m) <> drive(t, after(m))

# Laws
# ----

# LAW throttle_step_exact: every event moves the throttle and answers the actions R1-R4 say, for every state of the flags
# EXCLUDES: a timer armed while one runs or a commit is in flight, a
#   commit with no partial pending or after the stop, a partial kept
#   pending after its commit, a timer not re-armed for a pending partial,
#   a stop that leaves the timer running or does not await the commit, a
#   dropped request that keeps the timer, actions in another order
law throttle_step_exact:
  for g: Th.Gate
  for e: Th.Ev
  {Th.step(g, e) == step_spec(g, e) : Th.Moved}

# LAW throttle_one_commit: a step starts at most one commit, only when none is in flight, and then one is in flight
# EXCLUDES: two commits in flight, a commit that the throttle forgets
law throttle_one_commit:
  for +g: Th.Gate
  for e: Th.Ev
  {one_commit(g, Th.step(g, e)) == True{} : Bool}

# LAW throttle_commit_takes: a step that starts a commit had a partial pending and takes it
# EXCLUDES: a commit of nothing, the same partial committed twice
law throttle_commit_takes:
  for +g: Th.Gate
  for e: Th.Ev
  {takes(g, Th.step(g, e)) == True{} : Bool}

# LAW throttle_stopped_quiet: once stopped, no event starts a commit or a timer, and the throttle stays stopped
# EXCLUDES: a stale partial that lands after the outcome, a timer left
#   committing partials after the request ended
law throttle_stopped_quiet:
  for +g: Th.Gate
  for e: Th.Ev
  for s: {stopped(g) == True{} : Bool}
  {quiet(Th.step(g, e)) == True{} : Bool}

# LAW throttle_stop_ends: the stop and a dropped request start no commit and no timer, leave the throttle stopped and no timer running
# EXCLUDES: a stop or a drop that keeps the timer or starts a commit
law throttle_stop_ends:
  for +g: Th.Gate
  {ends(Th.step(g, Th.Finish{})) == True{} : Bool} & {ends(Th.step(g, Th.Quit{})) == True{} : Bool}

# LAW throttle_empty_ignored: a partial with no content changes nothing
# EXCLUDES: an opening event with no content kept as a partial
law throttle_empty_ignored:
  for +g: Th.Gate
  {Th.step(g, Th.Part{False{}}) == Th.Moved{g, []} : Th.Moved}

# LAW throttle_good_kept: every event keeps R5: never a timer and a commit at once, and a pending partial with no stop has one of them
# EXCLUDES: a pending partial left with no timer and no commit (never
#   committed), a timer running beside a commit
law throttle_good_kept:
  for +g: Th.Gate
  for e: Th.Ev
  for ok: {good(g) == True{} : Bool}
  {good(after(Th.step(g, e))) == True{} : Bool}

# LAW throttle_progress: when the running timer fires or the commit in flight settles with a partial pending and no stop, a commit or a timer starts
# EXCLUDES: a pending partial dropped when the timer fires or when a
#   commit settles
law throttle_progress:
  for +g: Th.Gate
  for +e: Th.Ev
  for ok: {good(g) == True{} : Bool}
  for w: {wakes(g, e) == True{} : Bool}
  {moves(actions(Th.step(g, e))) == True{} : Bool}

# LAW throttle_example: anchor: a throttle that saw nothing keeps R5; two partials with a commit between, a stop that awaits the commit, a partial after the stop; a drop with the timer running
# EXCLUDES: a spec that is wrong on the shipped cases
law throttle_example:
  {good(Th.start()) == True{} : Bool} &
  {drive([Th.Part{False{}}, Th.Part{True{}}, Th.Part{True{}}, Th.Fire{}, Th.Part{True{}}, Th.Settle{}, Th.Fire{}, Th.Finish{}, Th.Settle{}, Th.Part{True{}}], Th.start()) == [[], [Th.Keep{}, Th.Arm{}], [Th.Keep{}], [Th.Commit{}], [Th.Keep{}], [Th.Arm{}], [Th.Commit{}], [Th.Await{}], [], []] : List<&2, List<&2, Th.Act>>} &
  {drive([Th.Part{True{}}, Th.Quit{}, Th.Fire{}], Th.start()) == [[Th.Keep{}, Th.Arm{}], [Th.Abort{}], []] : List<&2, List<&2, Th.Act>>}

# LAWS (R6): the stepper of the compiled Bend core
# (bend/ffi_throttle.bend, driven by crates/eukhe-durable generation
# through `eukhe_bend::rules::throttle`). Each law is an open claim about
# FTh.open or FTh.step, stated with spec spellers built only from the wire
# primitives of bend/wire.bend (their round trips: laws/wire.bend).
#
# R6: the open is the empty input and answers an empty reply; a step is
#     an event: tag 0 a partial and whether it has content (a Bool), 1 the
#     timer fired, 2 the commit settled, 3 the stop, 4 a dropped request;
#     it answers the actions as a list of tags: 0 keep the partial, 1 arm
#     the timer, 2 start a commit, 3 abort the timer, 4 await the commit.
#     An open with any input answers the error form "throttle: malformed
#     open" and refuses every step with "throttle: the open was refused";
#     a malformed event (input left over included) answers "throttle:
#     malformed event" and keeps the throttle; never a default.

# Spec spellers
# -------------

# an event: its tag, then whether a partial has content
def spell_ev(e: Th.Ev, rest: String) -> String:
  match e:
    case Th.Part{b}:
      Wr.put_nat(0n, Wr.put_bool(b, rest))
    case Th.Fire{}:
      Wr.put_nat(1n, rest)
    case Th.Settle{}:
      Wr.put_nat(2n, rest)
    case Th.Finish{}:
      Wr.put_nat(3n, rest)
    case Th.Quit{}:
      Wr.put_nat(4n, rest)

# an action: its tag
def spell_act(a: Th.Act, rest: String) -> String:
  match a:
    case Th.Keep{}:
      Wr.put_nat(0n, rest)
    case Th.Arm{}:
      Wr.put_nat(1n, rest)
    case Th.Commit{}:
      Wr.put_nat(2n, rest)
    case Th.Abort{}:
      Wr.put_nat(3n, rest)
    case Th.Await{}:
      Wr.put_nat(4n, rest)

def spell_acts.items(acts: List<&2, Th.Act>, rest: String) -> String:
  match acts:
    case Nil{}:
      rest
    case a <> t:
      spell_act(a, spell_acts.items(t, rest))

# the actions: their count, then each action
def spell_acts(+acts: List<&2, Th.Act>) -> String:
  Wr.put_nat(List.length(&2, Th.Act, acts), spell_acts.items(acts, ""))

# the stepper after an event the model reads, and its reply
def spell_moved(m: Th.Moved) -> FTh.St & String:
  match m:
    case Th.Moved{g, acts}:
      (FTh.Live{g}, spell_acts(acts))

# the reply of a step or an open
def reply(r: FTh.St & String) -> String:
  match r:
    case (st, out):
      out

# Laws
# ----

# the open: the empty input opens a throttle that saw nothing with an
# empty reply; any other input opens the refused state with the error
# form
def open_spec(s: String) -> FTh.St & String:
  match s:
    case SNil{}:
      (FTh.Live{Th.start()}, "")
    case SCon{c, t}:
      (FTh.Shut{}, Wr.err("throttle: malformed open"))

# LAW throttle_ffi_open: the empty open answers a throttle that saw nothing and an empty reply; an open with any input opens the refused state with exactly the error form "throttle: malformed open"
# EXCLUDES: a throttle that starts pending, armed, in flight or stopped, a
#   default throttle for an open with input, another error text
law throttle_ffi_open:
  for s: String
  {FTh.open(s) == open_spec(s) : FTh.St & String}

# LAW throttle_ffi_step: on every throttle and every spelled event, the stepper moves as the model's step and answers its actions spelled
# EXCLUDES: an event read as another (a tag off by one, a flag misread), an
#   action spelled with another tag, actions lost, added or reordered
law throttle_ffi_step:
  for +g: Th.Gate
  for +e: Th.Ev
  {FTh.step(FTh.Live{g}, spell_ev(e, "")) == spell_moved(Th.step(g, e)) : FTh.St & String}

# LAW throttle_ffi_step_exact: every step the entry answers with a value (not the error form) on a throttle is a spelled event
# EXCLUDES: a default answer for a malformed event (a tag past 4, a
#   missing or malformed flag) or one with input left over
law throttle_ffi_step_exact:
  for +g: Th.Gate
  for +s: String
  for ok: {LawsBase.wire_opens_err(reply(FTh.step(FTh.Live{g}, s))) == False{} : Bool}
  exs e: Th.Ev
  {s == spell_ev(e, "") : String}

# LAW throttle_ffi_step_errors: a step the entry refuses on a throttle keeps the throttle and answers exactly the error form "throttle: malformed event"
# EXCLUDES: another error text, a malformed event that moves the throttle
law throttle_ffi_step_errors:
  for +g: Th.Gate
  for +s: String
  for e: {LawsBase.wire_opens_err(reply(FTh.step(FTh.Live{g}, s))) == True{} : Bool}
  {FTh.step(FTh.Live{g}, s) == (FTh.Live{g}, Wr.err("throttle: malformed event")) : FTh.St & String}

# LAW throttle_ffi_shut: a refused open answers every step with the error form "throttle: the open was refused"
# EXCLUDES: a refused open that answers actions
law throttle_ffi_shut:
  for s: String
  {FTh.step(FTh.Shut{}, s) == (FTh.Shut{}, Wr.err("throttle: the open was refused")) : FTh.St & String}

# the reply r, then the replies of the stepper fed the inputs ins, one
# step each from the state of r
def feed(ins: List<&2, String>, r: FTh.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> feed(t, FTh.step(st, i))

# LAW throttle_ffi_example: anchor: the bytes Rust sends and reads: a partial, an empty partial, a commit, a partial in flight, a re-armed timer, a stop that awaits, a malformed event, a refused open
# EXCLUDES: another spelling of an open, an event or a reply
law throttle_ffi_example:
  {feed(["0,T", "0,F", "1,", "0,T", "2,", "1,", "3,", "2,", "0,T", "5,", "1,x"], FTh.open("")) == ["", "2,0,1,", "0,", "1,2,", "1,0,", "1,1,", "1,2,", "1,4,", "0,", "0,", Wr.err("throttle: malformed event"), Wr.err("throttle: malformed event")] : List<&2, String>} &
  {feed(["0,T", "4,"], FTh.open("")) == ["", "2,0,1,", "1,3,"] : List<&2, String>} &
  {feed(["1,"], FTh.open("x")) == [Wr.err("throttle: malformed open"), Wr.err("throttle: the open was refused")] : List<&2, String>}
