# loop (spec): `/loop`, the prompt sent again after every turn until its
# stop condition is confirmed, restated as what a user can observe, over
# the types of bend/loop.bend.
# The laws of area loop (laws/loop/) are stated with these helpers. A spec:
# the shipped code never calls it.
#
# S1: a loop is on from `/loop` until it ends: armed (waiting for the
#     prompt), in a turn, judging (the condition command runs) or paused.
# S2: an automatic iteration is a turn the loop starts by itself (Submit).
#     The user's own acts are `/loop` (Enter) and a prompt (Prompt); a
#     history with neither is unattended.
# S3: the evidence of a condition is the exit status of its command, read
#     after the last turn. For `--until`, exit 0 shows the stop condition
#     and exit 1 shows it does not hold yet; for `--while` the reverse.
#     Nothing else shows either (exit 1 is the only "condition is false"
#     status; anything higher, no status, a timeout or a failed start is
#     the check breaking).
# S4: the bounds of an automatic iteration: the count of the start (one
#     fewer after each), the deadline of the start (the clock must be
#     before it), three failed turns in a row, the budget.
# S5: what starts or judges: Submit, Adopt, Judge, Resume. What waits:
#     Rest, Defer. Report tells the end.
# S6: an event that can be delivered twice after a crash: a stop, an
#     abort, a settled turn, a judged check (not blocked).

import Base
import ../../bend/loop.bend as Lp

# Projections
# -----------

def state(r: Lp.St & Lp.Act) -> Lp.St:
  (s, a) = r
  s

def act(r: Lp.St & Lp.Act) -> Lp.Act:
  (s, a) = r
  a

# the state after event e
def next(s: Lp.St, e: Lp.Ev) -> Lp.St:
  state(Lp.step(s, e))

# what the loop does at event e
def does(s: Lp.St, e: Lp.Ev) -> Lp.Act:
  act(Lp.step(s, e))

def phase(s: Lp.St) -> Lp.Phase:
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      p

def iter(s: Lp.St) -> Nat:
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      i

def left(s: Lp.St) -> Maybe<&2, Nat>:
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      l

def deadline(s: Lp.St) -> Maybe<&2, Nat>:
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      d

def cond(s: Lp.St) -> Lp.Cond:
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      c

def body(s: Lp.St) -> String:
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      b

def fails(s: Lp.St) -> Nat:
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      f

def last(s: Lp.St) -> Lp.Last:
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      x

# S1: phases
# ----------

def is_on(p: Lp.Phase) -> Bool:
  match p:
    case Lp.Off{}:
      False{}
    case Lp.Armed{}:
      True{}
    case Lp.Turn{}:
      True{}
    case Lp.Judging{}:
      True{}
    case Lp.Paused{}:
      True{}
    case Lp.Ended{w}:
      False{}

def is_turn(p: Lp.Phase) -> Bool:
  match p:
    case Lp.Off{}:
      False{}
    case Lp.Armed{}:
      False{}
    case Lp.Turn{}:
      True{}
    case Lp.Judging{}:
      False{}
    case Lp.Paused{}:
      False{}
    case Lp.Ended{w}:
      False{}

def is_judging(p: Lp.Phase) -> Bool:
  match p:
    case Lp.Off{}:
      False{}
    case Lp.Armed{}:
      False{}
    case Lp.Turn{}:
      False{}
    case Lp.Judging{}:
      True{}
    case Lp.Paused{}:
      False{}
    case Lp.Ended{w}:
      False{}

def end_is_satisfied(w: Lp.End) -> Bool:
  match w:
    case Lp.Satisfied{}:
      True{}
    case Lp.CheckBroke{}:
      False{}
    case Lp.OutOfTurns{}:
      False{}
    case Lp.OutOfTime{}:
      False{}
    case Lp.TurnsFailed{}:
      False{}
    case Lp.OutOfBudget{}:
      False{}
    case Lp.Stopped{}:
      False{}

# the loop ended with its stop condition confirmed
def is_satisfied(p: Lp.Phase) -> Bool:
  match p:
    case Lp.Off{}:
      False{}
    case Lp.Armed{}:
      False{}
    case Lp.Turn{}:
      False{}
    case Lp.Judging{}:
      False{}
    case Lp.Paused{}:
      False{}
    case Lp.Ended{w}:
      end_is_satisfied(w)

# S2: events and histories
# ------------------------

def is_enter(e: Lp.Ev) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      True{}
    case Lp.Stop{}:
      False{}
    case Lp.Abort{}:
      False{}
    case Lp.Prompt{t}:
      False{}
    case Lp.Settled{k, o, b, now, fu}:
      False{}
    case Lp.Judged{k, ev, b, now, fu}:
      False{}
    case Lp.Restart{}:
      False{}

def is_judged(e: Lp.Ev) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      False{}
    case Lp.Stop{}:
      False{}
    case Lp.Abort{}:
      False{}
    case Lp.Prompt{t}:
      False{}
    case Lp.Settled{k, o, b, now, fu}:
      False{}
    case Lp.Judged{k, ev, b, now, fu}:
      True{}
    case Lp.Restart{}:
      False{}

# the user's own act: `/loop` or a prompt
def is_user(e: Lp.Ev) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      True{}
    case Lp.Stop{}:
      False{}
    case Lp.Abort{}:
      False{}
    case Lp.Prompt{t}:
      True{}
    case Lp.Settled{k, o, b, now, fu}:
      False{}
    case Lp.Judged{k, ev, b, now, fu}:
      False{}
    case Lp.Restart{}:
      False{}

# no `/loop` in the history
def no_enter(h: List<&2, Lp.Ev>) -> Bool:
  match h:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Bool.not(is_enter(e)), no_enter(t))

# no act of the user in the history
def unattended(h: List<&2, Lp.Ev>) -> Bool:
  match h:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Bool.not(is_user(e)), unattended(t))

def out_ran(o: Lp.Out) -> Bool:
  match o:
    case Lp.Ran{}:
      True{}
    case Lp.Errored{}:
      False{}
    case Lp.Halted{}:
      False{}

def out_halted(o: Lp.Out) -> Bool:
  match o:
    case Lp.Ran{}:
      False{}
    case Lp.Errored{}:
      False{}
    case Lp.Halted{}:
      True{}

# a turn that ran to its end settled
def is_ran(e: Lp.Ev) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      False{}
    case Lp.Stop{}:
      False{}
    case Lp.Abort{}:
      False{}
    case Lp.Prompt{t}:
      False{}
    case Lp.Settled{k, o, b, now, fu}:
      out_ran(o)
    case Lp.Judged{k, ev, b, now, fu}:
      False{}
    case Lp.Restart{}:
      False{}

# no turn of the history ran to its end
def none_ran(h: List<&2, Lp.Ev>) -> Bool:
  match h:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Bool.not(is_ran(e)), none_ran(t))

# the event says the session is not idle
def blocked(e: Lp.Ev) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      False{}
    case Lp.Stop{}:
      False{}
    case Lp.Abort{}:
      False{}
    case Lp.Prompt{t}:
      False{}
    case Lp.Settled{k, o, b, now, fu}:
      b
    case Lp.Judged{k, ev, b, now, fu}:
      b
    case Lp.Restart{}:
      False{}

# the event says the budget funds no further turn
def unfunded(e: Lp.Ev) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      False{}
    case Lp.Stop{}:
      False{}
    case Lp.Abort{}:
      False{}
    case Lp.Prompt{t}:
      False{}
    case Lp.Settled{k, o, b, now, fu}:
      Bool.not(fu)
    case Lp.Judged{k, ev, b, now, fu}:
      Bool.not(fu)
    case Lp.Restart{}:
      False{}

# the event is no new `/loop`, and its clock (if it has one) is at or past d
def past(e: Lp.Ev, d: Nat) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      False{}
    case Lp.Stop{}:
      True{}
    case Lp.Abort{}:
      True{}
    case Lp.Prompt{t}:
      True{}
    case Lp.Settled{k, o, b, now, fu}:
      Nat.is_le(d, now)
    case Lp.Judged{k, ev, b, now, fu}:
      Nat.is_le(d, now)
    case Lp.Restart{}:
      True{}

# S6: an event that may be delivered twice
def once(e: Lp.Ev) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      False{}
    case Lp.Stop{}:
      True{}
    case Lp.Abort{}:
      True{}
    case Lp.Prompt{t}:
      False{}
    case Lp.Settled{k, o, b, now, fu}:
      Bool.not(b)
    case Lp.Judged{k, ev, b, now, fu}:
      Bool.not(b)
    case Lp.Restart{}:
      False{}

# S3: evidence
# ------------

def has_cond(c: Lp.Cond) -> Bool:
  match c:
    case Lp.NoCond{}:
      False{}
    case Lp.Until{cmd}:
      True{}
    case Lp.While{cmd}:
      True{}

# the command exited with status n
def exited_with(ev: Lp.Evid, n: Nat) -> Bool:
  match ev:
    case Lp.Exited{code}:
      Nat.is_eq(code, n)
    case Lp.NoStatus{}:
      False{}
    case Lp.TimedOut{}:
      False{}
    case Lp.SpawnFailed{}:
      False{}
    case Lp.Cancelled{}:
      False{}

# the evidence shows the stop condition of c
def shows_stop(c: Lp.Cond, ev: Lp.Evid) -> Bool:
  match c:
    case Lp.NoCond{}:
      False{}
    case Lp.Until{cmd}:
      exited_with(ev, 0n)
    case Lp.While{cmd}:
      exited_with(ev, 1n)

# the evidence shows the stop condition of c does not hold yet
def shows_go(c: Lp.Cond, ev: Lp.Evid) -> Bool:
  match c:
    case Lp.NoCond{}:
      False{}
    case Lp.Until{cmd}:
      exited_with(ev, 1n)
    case Lp.While{cmd}:
      exited_with(ev, 0n)

# the evidence decides something: the check was not cancelled
def decides(ev: Lp.Evid) -> Bool:
  match ev:
    case Lp.Exited{code}:
      True{}
    case Lp.NoStatus{}:
      True{}
    case Lp.TimedOut{}:
      True{}
    case Lp.SpawnFailed{}:
      True{}
    case Lp.Cancelled{}:
      False{}

# e is evidence read after the last turn of s, in an idle session, with
# the answer `shows`
def fresh_check(+s: Lp.St, k: Nat, b: Bool, shows: Bool) -> Bool:
  Bool.and(is_judging(phase(s)), Bool.and(Nat.is_eq(k, iter(s)), Bool.and(Bool.not(b), shows)))

# e is fresh evidence that shows the stop condition of s
def confirms(+s: Lp.St, e: Lp.Ev) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      False{}
    case Lp.Stop{}:
      False{}
    case Lp.Abort{}:
      False{}
    case Lp.Prompt{t}:
      False{}
    case Lp.Settled{k, o, b, now, fu}:
      False{}
    case Lp.Judged{k, ev, b, now, fu}:
      fresh_check(s, k, b, shows_stop(cond(s), ev))
    case Lp.Restart{}:
      False{}

# e is fresh evidence that shows the stop condition of s does not hold yet
def refutes(+s: Lp.St, e: Lp.Ev) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      False{}
    case Lp.Stop{}:
      False{}
    case Lp.Abort{}:
      False{}
    case Lp.Prompt{t}:
      False{}
    case Lp.Settled{k, o, b, now, fu}:
      False{}
    case Lp.Judged{k, ev, b, now, fu}:
      fresh_check(s, k, b, shows_go(cond(s), ev))
    case Lp.Restart{}:
      False{}

# the loop was not ended satisfied before e and is after it
def newly_satisfied(+s: Lp.St, e: Lp.Ev) -> Bool:
  Bool.and(Bool.not(is_satisfied(phase(s))), is_satisfied(phase(next(s, e))))

# S5: acts
# --------

def is_submit(a: Lp.Act) -> Bool:
  match a:
    case Lp.Rest{}:
      False{}
    case Lp.Submit{i, t}:
      True{}
    case Lp.Adopt{i}:
      False{}
    case Lp.Judge{i}:
      False{}
    case Lp.Resume{i, t}:
      False{}
    case Lp.Report{w}:
      False{}
    case Lp.Defer{}:
      False{}

def is_report(a: Lp.Act) -> Bool:
  match a:
    case Lp.Rest{}:
      False{}
    case Lp.Submit{i, t}:
      False{}
    case Lp.Adopt{i}:
      False{}
    case Lp.Judge{i}:
      False{}
    case Lp.Resume{i, t}:
      False{}
    case Lp.Report{w}:
      True{}
    case Lp.Defer{}:
      False{}

# the act starts a turn or a check
def starts(a: Lp.Act) -> Bool:
  match a:
    case Lp.Rest{}:
      False{}
    case Lp.Submit{i, t}:
      True{}
    case Lp.Adopt{i}:
      True{}
    case Lp.Judge{i}:
      True{}
    case Lp.Resume{i, t}:
      True{}
    case Lp.Report{w}:
      False{}
    case Lp.Defer{}:
      False{}

# the act waits: nothing starts, nothing is judged, nothing ends
def waits(a: Lp.Act) -> Bool:
  match a:
    case Lp.Rest{}:
      True{}
    case Lp.Submit{i, t}:
      False{}
    case Lp.Adopt{i}:
      False{}
    case Lp.Judge{i}:
      False{}
    case Lp.Resume{i, t}:
      False{}
    case Lp.Report{w}:
      False{}
    case Lp.Defer{}:
      True{}

def is_rest(a: Lp.Act) -> Bool:
  match a:
    case Lp.Rest{}:
      True{}
    case Lp.Submit{i, t}:
      False{}
    case Lp.Adopt{i}:
      False{}
    case Lp.Judge{i}:
      False{}
    case Lp.Resume{i, t}:
      False{}
    case Lp.Report{w}:
      False{}
    case Lp.Defer{}:
      False{}

# Histories
# ---------

# the state after the events of h, in order, from s
def after(h: List<&2, Lp.Ev>, s: Lp.St) -> Lp.St:
  match h:
    case Nil{}:
      s
    case Con{e, t}:
      after(t, next(s, e))

# what the loop does at each event of h, in order, from s
def acts(h: List<&2, Lp.Ev>, +s: Lp.St) -> List<&2, Lp.Act>:
  match h:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      does(s, e) <> acts(t, next(s, e))

def one_if(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# how many automatic iterations the acts start
def submits(as: List<&2, Lp.Act>) -> Nat:
  match as:
    case Nil{}:
      0n
    case Con{a, t}:
      Nat.add(one_if(is_submit(a)), submits(t))

# how many times the acts report an end
def reports(as: List<&2, Lp.Act>) -> Nat:
  match as:
    case Nil{}:
      0n
    case Con{a, t}:
      Nat.add(one_if(is_report(a)), reports(t))

# no act starts a turn or a check
def none_starts(as: List<&2, Lp.Act>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case Con{a, t}:
      Bool.and(Bool.not(starts(a)), none_starts(t))

# every act is Rest
def all_rest(as: List<&2, Lp.Act>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case Con{a, t}:
      Bool.and(is_rest(a), all_rest(t))

# the text an act sends, if it sends one, is b
def TextIs(a: Lp.Act, b: String) -> Type:
  match a:
    case Lp.Rest{}:
      Unit
    case Lp.Submit{i, t}:
      {t == b : String}
    case Lp.Adopt{i}:
      Unit
    case Lp.Judge{i}:
      Unit
    case Lp.Resume{i, t}:
      {t == b : String}
    case Lp.Report{w}:
      Unit
    case Lp.Defer{}:
      Unit

# every text the acts send is b
def TextsAre(as: List<&2, Lp.Act>, b: String) -> Type:
  match as:
    case Nil{}:
      Unit
    case Con{a, t}:
      TextIs(a, b) & TextsAre(t, b)
