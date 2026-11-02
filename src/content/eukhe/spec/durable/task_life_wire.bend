# durable (spec): the wire of the task lifecycle entry
# (bend/ffi_task_life.bend) as the laws of area task_life
# (laws/task_life.bend, section entry) read it: the requests and replies
# spelled with the wire primitives only (bend/wire.bend; their round
# trips: laws/wire.bend), what fits the wire, and the reader of a request.
# A spec: the shipped code never calls it.

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

# the reply to a request: the rules' decision, spelled as Rust reads it
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

# The reader: the request an input spells, read with the wire's decoders
# ----------------------------------------------------------------------

def r_policy(r: Wr.Dec<Nat>) -> Wr.Dec<Tl.Policy>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Tl.FailFast{}, s}
        case 1n:
          Wr.Got{Tl.AllSettled{}, s}
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_res(r: Wr.Dec<Nat>) -> Wr.Dec<Tl.Res>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Tl.RCompleted{}, s}
        case 1n:
          Wr.Got{Tl.RFailed{}, s}
        case 2n:
          Wr.Got{Tl.RAborted{}, s}
        case 3n:
          Wr.Got{Tl.ROrphaned{}, s}
        case 4n:
          Wr.Got{Tl.RFaulted{}, s}
        case 5n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_outcome.h(x: Tl.Res, r: Wr.Dec<Nat>) -> Wr.Dec<Tl.Outcome>:
  match r:
    case Wr.Got{h, s}:
      Wr.Got{Tl.Outcome{x, h}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_outcome(r: Wr.Dec<Tl.Res>) -> Wr.Dec<Tl.Outcome>:
  match r:
    case Wr.Got{x, s}:
      r_outcome.h(x, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_st.one(r: Wr.Dec<Nat>, k: Nat) -> Wr.Dec<Tl.St>:
  match r:
    case Wr.Got{c, s}:
      match k:
        case 0n:
          Wr.Got{Tl.Pending{c}, s}
        case 1n+u:
          Wr.Got{Tl.Running{c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_st.policy(c: Nat, r: Wr.Dec<Tl.Policy>) -> Wr.Dec<Tl.St>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{Tl.Waiting{c, p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_st.wait(r: Wr.Dec<Nat>) -> Wr.Dec<Tl.St>:
  match r:
    case Wr.Got{c, s}:
      r_st.policy(c, r_policy(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_st.out(r: Wr.Dec<Tl.Outcome>, k: Nat) -> Wr.Dec<Tl.St>:
  match r:
    case Wr.Got{o, s}:
      match k:
        case 0n:
          Wr.Got{Tl.Completing{o}, s}
        case 1n+u:
          Wr.Got{Tl.Terminal{o}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_st(r: Wr.Dec<Nat>) -> Wr.Dec<Tl.St>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          r_st.one(Wr.get_nat(s), 0n)
        case 1n:
          r_st.one(Wr.get_nat(s), 1n)
        case 2n:
          r_st.wait(Wr.get_nat(s))
        case 3n:
          r_st.out(r_outcome(r_res(Wr.get_nat(s))), 0n)
        case 4n:
          r_st.out(r_outcome(r_res(Wr.get_nat(s))), 1n)
        case 5n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_next.run(r: Wr.Dec<Nat>) -> Wr.Dec<Tl.Next>:
  match r:
    case Wr.Got{c, s}:
      Wr.Got{Tl.NRun{c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_next.policy(c: Nat, r: Wr.Dec<Tl.Policy>) -> Wr.Dec<Tl.Next>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{Tl.NWait{c, p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_next.wait(r: Wr.Dec<Nat>) -> Wr.Dec<Tl.Next>:
  match r:
    case Wr.Got{c, s}:
      r_next.policy(c, r_policy(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_next.end(r: Wr.Dec<Tl.Outcome>) -> Wr.Dec<Tl.Next>:
  match r:
    case Wr.Got{o, s}:
      Wr.Got{Tl.NEnd{o}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_next(r: Wr.Dec<Nat>) -> Wr.Dec<Tl.Next>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          r_next.run(Wr.get_nat(s))
        case 1n:
          r_next.wait(Wr.get_nat(s))
        case 2n:
          r_next.end(r_outcome(r_res(Wr.get_nat(s))))
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_ev.commit_h(n: Tl.Next, r: Wr.Dec<Bool>) -> Wr.Dec<Tl.Ev>:
  match r:
    case Wr.Got{h, s}:
      Wr.Got{Tl.Commit{n, h}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_ev.commit(r: Wr.Dec<Tl.Next>) -> Wr.Dec<Tl.Ev>:
  match r:
    case Wr.Got{n, s}:
      r_ev.commit_h(n, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_ev.settle_h(o: Tl.Outcome, r: Wr.Dec<Bool>) -> Wr.Dec<Tl.Ev>:
  match r:
    case Wr.Got{h, s}:
      Wr.Got{Tl.Settle{o, h}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_ev.settle(r: Wr.Dec<Tl.Outcome>) -> Wr.Dec<Tl.Ev>:
  match r:
    case Wr.Got{o, s}:
      r_ev.settle_h(o, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_ev.fin(r: Wr.Dec<Bool>) -> Wr.Dec<Tl.Ev>:
  match r:
    case Wr.Got{h, s}:
      Wr.Got{Tl.Finalize{h}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_ev(r: Wr.Dec<Nat>) -> Wr.Dec<Tl.Ev>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Tl.Reserve{}, s}
        case 1n:
          r_ev.commit(r_next(Wr.get_nat(s)))
        case 2n:
          Wr.Got{Tl.Requeue{}, s}
        case 3n:
          r_ev.settle(r_outcome(r_res(Wr.get_nat(s))))
        case 4n:
          r_ev.fin(Wr.get_bool(s))
        case 5n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_mark(r: Wr.Dec<Nat>) -> Wr.Dec<Tl.Mark>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Tl.Clear{}, s}
        case 1n:
          Wr.Got{Tl.Restart{}, s}
        case 2n:
          Wr.Got{Tl.Request{}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_row.mark(l: Bool, b: Bool, r: Wr.Dec<Tl.Mark>) -> Wr.Dec<Tl.Row>:
  match r:
    case Wr.Got{m, s}:
      Wr.Got{Tl.Row{l, b, m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_row.bg(l: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<Tl.Row>:
  match r:
    case Wr.Got{b, s}:
      r_row.mark(l, b, r_mark(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_row.live(r: Wr.Dec<Bool>) -> Wr.Dec<Tl.Row>:
  match r:
    case Wr.Got{l, s}:
      r_row.bg(l, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_row(s: String) -> Wr.Dec<Tl.Row>:
  r_row.live(Wr.get_bool(s))

def r_req.step_e(x: Tl.St, r: Wr.Dec<Tl.Ev>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{e, s}:
      Wr.Got{FTl.QStep{x, e}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.step(r: Wr.Dec<Tl.St>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{x, s}:
      r_req.step_e(x, r_ev(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.resume(r: Wr.Dec<Tl.St>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{FTl.QResume{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.join_f(p: Tl.Policy, ls: List<&2, Bool>, r: Wr.Dec<List<&2, Bool>>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{fs, s}:
      Wr.Got{FTl.QJoin{p, ls, fs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.join_l(p: Tl.Policy, r: Wr.Dec<List<&2, Bool>>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{ls, s}:
      r_req.join_f(p, ls, Wr.get_list(~Bool, ~Wr.get_bool, s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.join(r: Wr.Dec<Tl.Policy>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{p, s}:
      r_req.join_l(p, Wr.get_list(~Bool, ~Wr.get_bool, s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.merge_b(a: Tl.Mark, r: Wr.Dec<Tl.Mark>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{FTl.QMerge{a, b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.merge(r: Wr.Dec<Tl.Mark>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{a, s}:
      r_req.merge_b(a, r_mark(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.cascade_r(x: Tl.St, m: Tl.Mark, r: Wr.Dec<List<&2, Tl.Row>>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{rs, s}:
      Wr.Got{FTl.QCascade{x, m, rs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.cascade_m(x: Tl.St, r: Wr.Dec<Tl.Mark>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{m, s}:
      r_req.cascade_r(x, m, Wr.get_list(~Tl.Row, ~r_row, s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.cascade(r: Wr.Dec<Tl.St>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{x, s}:
      r_req.cascade_m(x, r_mark(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req(r: Wr.Dec<Nat>) -> Wr.Dec<FTl.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          r_req.step(r_st(Wr.get_nat(s)))
        case 1n:
          r_req.resume(r_st(Wr.get_nat(s)))
        case 2n:
          r_req.join(r_policy(Wr.get_nat(s)))
        case 3n:
          r_req.merge(r_mark(Wr.get_nat(s)))
        case 4n:
          r_req.cascade(r_st(Wr.get_nat(s)))
        case 5n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_whole.end(b: Bool, q: FTl.Req) -> Maybe<&2, FTl.Req>:
  match b:
    case True{}:
      Some{q}
    case False{}:
      None{}

def r_whole(r: Wr.Dec<FTl.Req>) -> Maybe<&2, FTl.Req>:
  match r:
    case Wr.Got{q, s}:
      r_whole.end(Wr.end(s), q)
    case Wr.Bad{}:
      None{}

# the request s spells whole, with nothing after it
def read(s: String) -> Maybe<&2, FTl.Req>:
  r_whole(r_req(Wr.get_nat(s)))
