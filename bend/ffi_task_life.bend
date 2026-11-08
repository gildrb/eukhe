# ffi_task_life: the compiled Bend core's entry for the lifecycle rules of
# a durable task (bend/task_life.bend). Rust
# `eukhe_bend::rules::task_life` calls it through `eukhe_bend::call` from
# the scheduler of crates/eukhe-durable (harness/scheduler/life.rs).
#
# Request (crates/eukhe-bend/WIRE.md): a tag, then its fields.
#   0 step:    a state, then a transition
#   1 resume:  a state
#   2 join:    a policy, the awaited tasks that are live (List<Bool>), the
#              awaited tasks that failed (List<Bool>)
#   3 merge:   a mark, then the mark to add
#   4 cascade: the owner's state and mark, then the reached tasks
#              (List<Row>)
# A state: tag 0 pending, 1 running (then the checkpoint handle, a Nat), 2
# waiting (the checkpoint handle, then the policy), 3 completing, 4
# terminal (then the outcome). A policy: 0 failFast, 1 allSettled. An
# outcome: how it ended (0 completed, 1 failed, 2 aborted, 3 orphaned, 4
# faulted), then the payload handle (Nat). A transition: 0 reserve, 1
# commit (the next state: 0 running and its checkpoint, 1 waiting and its
# checkpoint and policy, 2 an outcome; then whether owned work holds, a
# Bool), 2 requeue, 3 settle (an outcome, then holds), 4 finalize (holds).
# A mark: 0 none, 1 restart, 2 request. A row: live, background (Bools),
# then its mark.
# Reply: step: 0 then why (0 ended, 1 held, 2 not running, 3 not held) | 1
# then the next state; resume: the state, then the failFast check (Bool);
# join: whether the task may run (Bool), then the marks (List<Bool>);
# merge: the mark; cascade: the marks (List<Mark>).
# Any other input (an unknown tag, a malformed field, input left after the
# request) answers the error form "task_life: malformed request", never a
# default. laws/task_life.bend (section entry) states this file's laws.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./task_life.bend as Tl

# A request of the entry
type Req is Data:
  QStep{s: Tl.St, e: Tl.Ev}
  QResume{s: Tl.St}
  QJoin{p: Tl.Policy, live: List<&2, Bool>, failed: List<&2, Bool>}
  QMerge{a: Tl.Mark, b: Tl.Mark}
  QCascade{s: Tl.St, m: Tl.Mark, rows: List<&2, Tl.Row>}

# Decoders
# --------

def get_policy(r: W.Dec<Nat>) -> W.Dec<Tl.Policy>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Tl.FailFast{}, s}
        case 1n:
          W.Got{Tl.AllSettled{}, s}
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_res(r: W.Dec<Nat>) -> W.Dec<Tl.Res>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Tl.RCompleted{}, s}
        case 1n:
          W.Got{Tl.RFailed{}, s}
        case 2n:
          W.Got{Tl.RAborted{}, s}
        case 3n:
          W.Got{Tl.ROrphaned{}, s}
        case 4n:
          W.Got{Tl.RFaulted{}, s}
        case 5n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_outcome.h(x: Tl.Res, r: W.Dec<Nat>) -> W.Dec<Tl.Outcome>:
  match r:
    case W.Got{h, s}:
      W.Got{Tl.Outcome{x, h}, s}
    case W.Bad{}:
      W.Bad{}

def get_outcome(r: W.Dec<Tl.Res>) -> W.Dec<Tl.Outcome>:
  match r:
    case W.Got{x, s}:
      get_outcome.h(x, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# a live state with one checkpoint: k 0 pending, 1 running
def get_st.one(r: W.Dec<Nat>, k: Nat) -> W.Dec<Tl.St>:
  match r:
    case W.Got{c, s}:
      match k:
        case 0n:
          W.Got{Tl.Pending{c}, s}
        case 1n+u:
          W.Got{Tl.Running{c}, s}
    case W.Bad{}:
      W.Bad{}

def get_st.policy(c: Nat, r: W.Dec<Tl.Policy>) -> W.Dec<Tl.St>:
  match r:
    case W.Got{p, s}:
      W.Got{Tl.Waiting{c, p}, s}
    case W.Bad{}:
      W.Bad{}

def get_st.wait(r: W.Dec<Nat>) -> W.Dec<Tl.St>:
  match r:
    case W.Got{c, s}:
      get_st.policy(c, get_policy(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# a state with an outcome: k 0 completing, 1 terminal
def get_st.out(r: W.Dec<Tl.Outcome>, k: Nat) -> W.Dec<Tl.St>:
  match r:
    case W.Got{o, s}:
      match k:
        case 0n:
          W.Got{Tl.Completing{o}, s}
        case 1n+u:
          W.Got{Tl.Terminal{o}, s}
    case W.Bad{}:
      W.Bad{}

def get_st(r: W.Dec<Nat>) -> W.Dec<Tl.St>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_st.one(W.get_nat(s), 0n)
        case 1n:
          get_st.one(W.get_nat(s), 1n)
        case 2n:
          get_st.wait(W.get_nat(s))
        case 3n:
          get_st.out(get_outcome(get_res(W.get_nat(s))), 0n)
        case 4n:
          get_st.out(get_outcome(get_res(W.get_nat(s))), 1n)
        case 5n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_next.run(r: W.Dec<Nat>) -> W.Dec<Tl.Next>:
  match r:
    case W.Got{c, s}:
      W.Got{Tl.NRun{c}, s}
    case W.Bad{}:
      W.Bad{}

def get_next.policy(c: Nat, r: W.Dec<Tl.Policy>) -> W.Dec<Tl.Next>:
  match r:
    case W.Got{p, s}:
      W.Got{Tl.NWait{c, p}, s}
    case W.Bad{}:
      W.Bad{}

def get_next.wait(r: W.Dec<Nat>) -> W.Dec<Tl.Next>:
  match r:
    case W.Got{c, s}:
      get_next.policy(c, get_policy(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_next.end(r: W.Dec<Tl.Outcome>) -> W.Dec<Tl.Next>:
  match r:
    case W.Got{o, s}:
      W.Got{Tl.NEnd{o}, s}
    case W.Bad{}:
      W.Bad{}

def get_next(r: W.Dec<Nat>) -> W.Dec<Tl.Next>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_next.run(W.get_nat(s))
        case 1n:
          get_next.wait(W.get_nat(s))
        case 2n:
          get_next.end(get_outcome(get_res(W.get_nat(s))))
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_ev.commit_h(n: Tl.Next, r: W.Dec<Bool>) -> W.Dec<Tl.Ev>:
  match r:
    case W.Got{h, s}:
      W.Got{Tl.Commit{n, h}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.commit(r: W.Dec<Tl.Next>) -> W.Dec<Tl.Ev>:
  match r:
    case W.Got{n, s}:
      get_ev.commit_h(n, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.settle_h(o: Tl.Outcome, r: W.Dec<Bool>) -> W.Dec<Tl.Ev>:
  match r:
    case W.Got{h, s}:
      W.Got{Tl.Settle{o, h}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.settle(r: W.Dec<Tl.Outcome>) -> W.Dec<Tl.Ev>:
  match r:
    case W.Got{o, s}:
      get_ev.settle_h(o, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.fin(r: W.Dec<Bool>) -> W.Dec<Tl.Ev>:
  match r:
    case W.Got{h, s}:
      W.Got{Tl.Finalize{h}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev(r: W.Dec<Nat>) -> W.Dec<Tl.Ev>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Tl.Reserve{}, s}
        case 1n:
          get_ev.commit(get_next(W.get_nat(s)))
        case 2n:
          W.Got{Tl.Requeue{}, s}
        case 3n:
          get_ev.settle(get_outcome(get_res(W.get_nat(s))))
        case 4n:
          get_ev.fin(W.get_bool(s))
        case 5n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_mark(r: W.Dec<Nat>) -> W.Dec<Tl.Mark>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Tl.Clear{}, s}
        case 1n:
          W.Got{Tl.Restart{}, s}
        case 2n:
          W.Got{Tl.Request{}, s}
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_row.mark(l: Bool, b: Bool, r: W.Dec<Tl.Mark>) -> W.Dec<Tl.Row>:
  match r:
    case W.Got{m, s}:
      W.Got{Tl.Row{l, b, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_row.bg(l: Bool, r: W.Dec<Bool>) -> W.Dec<Tl.Row>:
  match r:
    case W.Got{b, s}:
      get_row.mark(l, b, get_mark(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_row.live(r: W.Dec<Bool>) -> W.Dec<Tl.Row>:
  match r:
    case W.Got{l, s}:
      get_row.bg(l, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

# a row at the start of s
def get_row(s: String) -> W.Dec<Tl.Row>:
  get_row.live(W.get_bool(s))

def get_req.step_e(x: Tl.St, r: W.Dec<Tl.Ev>) -> W.Dec<Req>:
  match r:
    case W.Got{e, s}:
      W.Got{QStep{x, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.step(r: W.Dec<Tl.St>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      get_req.step_e(x, get_ev(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.resume(r: W.Dec<Tl.St>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QResume{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.join_f(p: Tl.Policy, ls: List<&2, Bool>, r: W.Dec<List<&2, Bool>>) -> W.Dec<Req>:
  match r:
    case W.Got{fs, s}:
      W.Got{QJoin{p, ls, fs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.join_l(p: Tl.Policy, r: W.Dec<List<&2, Bool>>) -> W.Dec<Req>:
  match r:
    case W.Got{ls, s}:
      get_req.join_f(p, ls, W.get_list(~Bool, ~W.get_bool, s))
    case W.Bad{}:
      W.Bad{}

def get_req.join(r: W.Dec<Tl.Policy>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      get_req.join_l(p, W.get_list(~Bool, ~W.get_bool, s))
    case W.Bad{}:
      W.Bad{}

def get_req.merge_b(a: Tl.Mark, r: W.Dec<Tl.Mark>) -> W.Dec<Req>:
  match r:
    case W.Got{b, s}:
      W.Got{QMerge{a, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.merge(r: W.Dec<Tl.Mark>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      get_req.merge_b(a, get_mark(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.cascade_r(x: Tl.St, m: Tl.Mark, r: W.Dec<List<&2, Tl.Row>>) -> W.Dec<Req>:
  match r:
    case W.Got{rs, s}:
      W.Got{QCascade{x, m, rs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.cascade_m(x: Tl.St, r: W.Dec<Tl.Mark>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      get_req.cascade_r(x, m, W.get_list(~Tl.Row, ~get_row, s))
    case W.Bad{}:
      W.Bad{}

def get_req.cascade(r: W.Dec<Tl.St>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      get_req.cascade_m(x, get_mark(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# the request whose tag r read
def get_req(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_req.step(get_st(W.get_nat(s)))
        case 1n:
          get_req.resume(get_st(W.get_nat(s)))
        case 2n:
          get_req.join(get_policy(W.get_nat(s)))
        case 3n:
          get_req.merge(get_mark(W.get_nat(s)))
        case 4n:
          get_req.cascade(get_st(W.get_nat(s)))
        case 5n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# Encoders
# --------

def put_policy(p: Tl.Policy, rest: String) -> String:
  match p:
    case Tl.FailFast{}:
      W.put_nat(0n, rest)
    case Tl.AllSettled{}:
      W.put_nat(1n, rest)

def put_res(x: Tl.Res, rest: String) -> String:
  match x:
    case Tl.RCompleted{}:
      W.put_nat(0n, rest)
    case Tl.RFailed{}:
      W.put_nat(1n, rest)
    case Tl.RAborted{}:
      W.put_nat(2n, rest)
    case Tl.ROrphaned{}:
      W.put_nat(3n, rest)
    case Tl.RFaulted{}:
      W.put_nat(4n, rest)

def put_outcome(o: Tl.Outcome, rest: String) -> String:
  match o:
    case Tl.Outcome{x, h}:
      put_res(x, W.put_nat(h, rest))

def put_st(x: Tl.St, rest: String) -> String:
  match x:
    case Tl.Pending{c}:
      W.put_nat(0n, W.put_nat(c, rest))
    case Tl.Running{c}:
      W.put_nat(1n, W.put_nat(c, rest))
    case Tl.Waiting{c, p}:
      W.put_nat(2n, W.put_nat(c, put_policy(p, rest)))
    case Tl.Completing{o}:
      W.put_nat(3n, put_outcome(o, rest))
    case Tl.Terminal{o}:
      W.put_nat(4n, put_outcome(o, rest))

def put_why(y: Tl.Why, rest: String) -> String:
  match y:
    case Tl.Ended{}:
      W.put_nat(0n, rest)
    case Tl.Held{}:
      W.put_nat(1n, rest)
    case Tl.NotRunning{}:
      W.put_nat(2n, rest)
    case Tl.NotHeld{}:
      W.put_nat(3n, rest)

def put_mark(m: Tl.Mark, rest: String) -> String:
  match m:
    case Tl.Clear{}:
      W.put_nat(0n, rest)
    case Tl.Restart{}:
      W.put_nat(1n, rest)
    case Tl.Request{}:
      W.put_nat(2n, rest)

def put_stepped(r: Result<&2, &2, Tl.Why, Tl.St>) -> String:
  match r:
    case Fail{y}:
      W.put_nat(0n, put_why(y, ""))
    case Done{x}:
      W.put_nat(1n, put_st(x, ""))

def put_resumed(r: Tl.St & Bool) -> String:
  (x, b) = r
  put_st(x, W.put_bool(b, ""))

def put_joined(r: Bool & List<&2, Bool>) -> String:
  (ok, ms) = r
  W.put_bool(ok, W.put_list(~Bool, ~W.put_bool, ms, ""))

# the reply of a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case QStep{x, e}:
      put_stepped(Tl.step(x, e))
    case QResume{x}:
      put_resumed(Tl.resume(x))
    case QJoin{p, ls, fs}:
      put_joined(Tl.join(p, ls, fs))
    case QMerge{a, b}:
      put_mark(Tl.merge(a, b), "")
    case QCascade{x, m, rs}:
      W.put_list(~Tl.Mark, ~put_mark, Tl.cascade(x, m, rs), "")

# The entry
# ---------

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("task_life: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("task_life: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(W.get_nat(input)))
