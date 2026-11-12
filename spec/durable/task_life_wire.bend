# durable (spec): the wire of the task lifecycle entry
# (bend/ffi_task_life.bend) as the laws of area task_life
# (laws/task_life.bend, section entry) read it: the requests and replies
# spelled with the wire primitives only (bend/wire.bend; their round
# trips: laws/wire.bend), and what fits the wire. A spec: the shipped code
# never calls it.

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase

# Spellers: a request as Rust writes it
# -------------------------------------

def w_policy(p: Tl.Policy, rest: String) -> String:
  match p:
    case Tl.FailFast{}:
      Wr.put_nat(0n, rest)
    case Tl.AllSettled{}:
      Wr.put_nat(1n, rest)

def w_res(x: Tl.Res) -> Nat:
  match x:
    case Tl.RCompleted{}:
      0n
    case Tl.RFailed{}:
      1n
    case Tl.RAborted{}:
      2n
    case Tl.ROrphaned{}:
      3n
    case Tl.RFaulted{}:
      4n

def w_outcome(o: Tl.Outcome, rest: String) -> String:
  match o:
    case Tl.Outcome{x, h}:
      Wr.put_nat(w_res(x), Wr.put_nat(h, rest))

def w_st(x: Tl.St, rest: String) -> String:
  match x:
    case Tl.Pending{c}:
      Wr.put_nat(0n, Wr.put_nat(c, rest))
    case Tl.Running{c}:
      Wr.put_nat(1n, Wr.put_nat(c, rest))
    case Tl.Waiting{c, p}:
      Wr.put_nat(2n, Wr.put_nat(c, w_policy(p, rest)))
    case Tl.Completing{o}:
      Wr.put_nat(3n, w_outcome(o, rest))
    case Tl.Terminal{o}:
      Wr.put_nat(4n, w_outcome(o, rest))

def w_next(n: Tl.Next, rest: String) -> String:
  match n:
    case Tl.NRun{c}:
      Wr.put_nat(0n, Wr.put_nat(c, rest))
    case Tl.NWait{c, p}:
      Wr.put_nat(1n, Wr.put_nat(c, w_policy(p, rest)))
    case Tl.NEnd{o}:
      Wr.put_nat(2n, w_outcome(o, rest))

def w_ev(e: Tl.Ev, rest: String) -> String:
  match e:
    case Tl.Reserve{}:
      Wr.put_nat(0n, rest)
    case Tl.Commit{n, h}:
      Wr.put_nat(1n, w_next(n, Wr.put_bool(h, rest)))
    case Tl.Requeue{}:
      Wr.put_nat(2n, rest)
    case Tl.Settle{o, h}:
      Wr.put_nat(3n, w_outcome(o, Wr.put_bool(h, rest)))
    case Tl.Finalize{h}:
      Wr.put_nat(4n, Wr.put_bool(h, rest))

def w_mark(m: Tl.Mark, rest: String) -> String:
  match m:
    case Tl.Clear{}:
      Wr.put_nat(0n, rest)
    case Tl.Restart{}:
      Wr.put_nat(1n, rest)
    case Tl.Request{}:
      Wr.put_nat(2n, rest)

def w_row(r: Tl.Row, rest: String) -> String:
  match r:
    case Tl.Row{l, b, m}:
      Wr.put_bool(l, Wr.put_bool(b, w_mark(m, rest)))

def w_bools(xs: List<&2, Bool>, rest: String) -> String:
  Wr.put_list(~Bool, ~Wr.put_bool, xs, rest)

# a request, then rest
def w_req(q: FTl.Req, rest: String) -> String:
  match q:
    case FTl.QStep{x, e}:
      Wr.put_nat(0n, w_st(x, w_ev(e, rest)))
    case FTl.QResume{x}:
      Wr.put_nat(1n, w_st(x, rest))
    case FTl.QJoin{p, ls, fs}:
      Wr.put_nat(2n, w_policy(p, w_bools(ls, w_bools(fs, rest))))
    case FTl.QMerge{a, b}:
      Wr.put_nat(3n, w_mark(a, w_mark(b, rest)))
    case FTl.QCascade{x, m, rs}:
      Wr.put_nat(4n, w_st(x, w_mark(m, Wr.put_list(~Tl.Row, ~w_row, rs, rest))))

# Spellers: the reply, as Rust reads it
# -------------------------------------

def w_why(y: Tl.Why) -> Nat:
  match y:
    case Tl.Ended{}:
      0n
    case Tl.Held{}:
      1n
    case Tl.NotRunning{}:
      2n
    case Tl.NotHeld{}:
      3n

def w_stepped(r: Result<&2, &2, Tl.Why, Tl.St>) -> String:
  match r:
    case Fail{y}:
      Wr.put_nat(0n, Wr.put_nat(w_why(y), ""))
    case Done{x}:
      Wr.put_nat(1n, w_st(x, ""))

def w_resumed(r: Tl.St & Bool) -> String:
  (x, b) = r
  w_st(x, Wr.put_bool(b, ""))

def w_joined(r: Bool & List<&2, Bool>) -> String:
  (ok, ms) = r
  Wr.put_bool(ok, w_bools(ms, ""))

# the reply to a request: the rules' decision, spelled as Rust reads it.
# The rules are the model's (bend/task_life.bend); the laws of
# laws/task_life.bend state them: step by task_life_live_steps,
# task_life_only_running_commits, task_life_running_commits,
# task_life_held_steps and task_life_terminal_absorbs; resume by
# task_life_resume_moves_only_running, task_life_resume_rechecks_fail_fast
# and task_life_resume_rechecks_only_fail_fast; join by
# task_life_join_may_run, task_life_join_marks_live_unfailed,
# task_life_join_all_settled_quiet, task_life_join_fail_fast_quiet and
# task_life_join_fail_fast_aborts; merge by task_life_mark_merge; cascade
# by task_life_cascade_keeps_others, task_life_cascade_needs_intent,
# task_life_cascade_request and task_life_cascade_restart
def w_reply(q: FTl.Req) -> String:
  match q:
    case FTl.QStep{x, e}:
      w_stepped(Tl.step(x, e))
    case FTl.QResume{x}:
      w_resumed(Tl.resume(x))
    case FTl.QJoin{p, ls, fs}:
      w_joined(Tl.join(p, ls, fs))
    case FTl.QMerge{a, b}:
      w_mark(Tl.merge(a, b), "")
    case FTl.QCascade{x, m, rs}:
      Wr.put_list(~Tl.Mark, ~w_mark, Tl.cascade(x, m, rs), "")

# Bounds: every handle and count of a request fits the wire
# ----------------------------------------------------------

def fit_outcome(o: Tl.Outcome) -> Bool:
  match o:
    case Tl.Outcome{x, h}:
      LawsBase.wire_fits(h)

def fit_st(x: Tl.St) -> Bool:
  match x:
    case Tl.Pending{c}:
      LawsBase.wire_fits(c)
    case Tl.Running{c}:
      LawsBase.wire_fits(c)
    case Tl.Waiting{c, p}:
      LawsBase.wire_fits(c)
    case Tl.Completing{o}:
      fit_outcome(o)
    case Tl.Terminal{o}:
      fit_outcome(o)

def fit_next(n: Tl.Next) -> Bool:
  match n:
    case Tl.NRun{c}:
      LawsBase.wire_fits(c)
    case Tl.NWait{c, p}:
      LawsBase.wire_fits(c)
    case Tl.NEnd{o}:
      fit_outcome(o)

def fit_ev(e: Tl.Ev) -> Bool:
  match e:
    case Tl.Reserve{}:
      True{}
    case Tl.Commit{n, h}:
      fit_next(n)
    case Tl.Requeue{}:
      True{}
    case Tl.Settle{o, h}:
      fit_outcome(o)
    case Tl.Finalize{h}:
      True{}

def fit_req(q: FTl.Req) -> Bool:
  match q:
    case FTl.QStep{x, e}:
      Bool.and(fit_st(x), fit_ev(e))
    case FTl.QResume{x}:
      fit_st(x)
    case FTl.QJoin{p, ls, fs}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Bool, ls)), LawsBase.wire_fits(List.length(&2, Bool, fs)))
    case FTl.QMerge{a, b}:
      True{}
    case FTl.QCascade{x, m, rs}:
      Bool.and(fit_st(x), LawsBase.wire_fits(List.length(&2, Tl.Row, rs)))
