# eukhe: lemmas of the entry proofs of area task_life: the entry's
# decoder reads every input as the laws' reader does (ter.*: stage by
# stage; the row list by its item loop, ter.list_go)

import Base
import ../../../bend/task_life.bend as Tl
import ../../../bend/ffi_task_life.bend as FTl
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../spec/durable/task_life_wire.bend as SpW

# Tags and fields
# ---------------

def ter.policy(d: Wr.Dec<Nat>) -> {FTl.get_policy(d) == SpW.r_policy(d) : Wr.Dec<Tl.Policy>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def ter.res(d: Wr.Dec<Nat>) -> {FTl.get_res(d) == SpW.r_res(d) : Wr.Dec<Tl.Res>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n+u:
          {==}
    case Wr.Bad{}:
      {==}

def ter.mark(d: Wr.Dec<Nat>) -> {FTl.get_mark(d) == SpW.r_mark(d) : Wr.Dec<Tl.Mark>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def ter.outcome_h(x: Tl.Res, d: Wr.Dec<Nat>) -> {FTl.get_outcome.h(x, d) == SpW.r_outcome.h(x, d) : Wr.Dec<Tl.Outcome>}:
  match d:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.outcome(d: Wr.Dec<Tl.Res>) -> {FTl.get_outcome(d) == SpW.r_outcome(d) : Wr.Dec<Tl.Outcome>}:
  match d:
    case Wr.Got{x, s}:
      ter.outcome_h(x, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ter.out2(+d: Wr.Dec<Nat>) -> {FTl.get_outcome(FTl.get_res(d)) == SpW.r_outcome(SpW.r_res(d)) : Wr.Dec<Tl.Outcome>}:
  %ter.res(d) : {FTl.get_outcome(FTl.get_res(d)) == SpW.r_outcome(_) : Wr.Dec<Tl.Outcome>}
  ter.outcome(FTl.get_res(d))

# States
# ------

def ter.st_one(d: Wr.Dec<Nat>, k: Nat) -> {FTl.get_st.one(d, k) == SpW.r_st.one(d, k) : Wr.Dec<Tl.St>}:
  match d:
    case Wr.Got{c, s}:
      match k:
        case 0n:
          {==}
        case 1n+u:
          {==}
    case Wr.Bad{}:
      {==}

def ter.st_policy(c: Nat, d: Wr.Dec<Tl.Policy>) -> {FTl.get_st.policy(c, d) == SpW.r_st.policy(c, d) : Wr.Dec<Tl.St>}:
  match d:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.st_wait(d: Wr.Dec<Nat>) -> {FTl.get_st.wait(d) == SpW.r_st.wait(d) : Wr.Dec<Tl.St>}:
  match d:
    case Wr.Got{+c, +s}:
      %ter.policy(Wr.get_nat(s)) : {FTl.get_st.policy(c, FTl.get_policy(Wr.get_nat(s))) == SpW.r_st.policy(c, _) : Wr.Dec<Tl.St>}
      ter.st_policy(c, FTl.get_policy(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def ter.st_out(d: Wr.Dec<Tl.Outcome>, k: Nat) -> {FTl.get_st.out(d, k) == SpW.r_st.out(d, k) : Wr.Dec<Tl.St>}:
  match d:
    case Wr.Got{o, s}:
      match k:
        case 0n:
          {==}
        case 1n+u:
          {==}
    case Wr.Bad{}:
      {==}

def ter.st(d: Wr.Dec<Nat>) -> {FTl.get_st(d) == SpW.r_st(d) : Wr.Dec<Tl.St>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          ter.st_one(Wr.get_nat(s), 0n)
        case 1n:
          ter.st_one(Wr.get_nat(s), 1n)
        case 2n:
          ter.st_wait(Wr.get_nat(s))
        case 3n:
          %ter.out2(Wr.get_nat(s)) : {FTl.get_st.out(FTl.get_outcome(FTl.get_res(Wr.get_nat(s))), 0n) == SpW.r_st.out(_, 0n) : Wr.Dec<Tl.St>}
          ter.st_out(FTl.get_outcome(FTl.get_res(Wr.get_nat(s))), 0n)
        case 4n:
          %ter.out2(Wr.get_nat(s)) : {FTl.get_st.out(FTl.get_outcome(FTl.get_res(Wr.get_nat(s))), 1n) == SpW.r_st.out(_, 1n) : Wr.Dec<Tl.St>}
          ter.st_out(FTl.get_outcome(FTl.get_res(Wr.get_nat(s))), 1n)
        case 5n+u:
          {==}
    case Wr.Bad{}:
      {==}

# Transitions
# -----------

def ter.next_run(d: Wr.Dec<Nat>) -> {FTl.get_next.run(d) == SpW.r_next.run(d) : Wr.Dec<Tl.Next>}:
  match d:
    case Wr.Got{c, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.next_policy(c: Nat, d: Wr.Dec<Tl.Policy>) -> {FTl.get_next.policy(c, d) == SpW.r_next.policy(c, d) : Wr.Dec<Tl.Next>}:
  match d:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.next_wait(d: Wr.Dec<Nat>) -> {FTl.get_next.wait(d) == SpW.r_next.wait(d) : Wr.Dec<Tl.Next>}:
  match d:
    case Wr.Got{+c, +s}:
      %ter.policy(Wr.get_nat(s)) : {FTl.get_next.policy(c, FTl.get_policy(Wr.get_nat(s))) == SpW.r_next.policy(c, _) : Wr.Dec<Tl.Next>}
      ter.next_policy(c, FTl.get_policy(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def ter.next_end(d: Wr.Dec<Tl.Outcome>) -> {FTl.get_next.end(d) == SpW.r_next.end(d) : Wr.Dec<Tl.Next>}:
  match d:
    case Wr.Got{o, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.next(d: Wr.Dec<Nat>) -> {FTl.get_next(d) == SpW.r_next(d) : Wr.Dec<Tl.Next>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          ter.next_run(Wr.get_nat(s))
        case 1n:
          ter.next_wait(Wr.get_nat(s))
        case 2n:
          %ter.out2(Wr.get_nat(s)) : {FTl.get_next.end(FTl.get_outcome(FTl.get_res(Wr.get_nat(s)))) == SpW.r_next.end(_) : Wr.Dec<Tl.Next>}
          ter.next_end(FTl.get_outcome(FTl.get_res(Wr.get_nat(s))))
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def ter.ev_commit_h(n: Tl.Next, d: Wr.Dec<Bool>) -> {FTl.get_ev.commit_h(n, d) == SpW.r_ev.commit_h(n, d) : Wr.Dec<Tl.Ev>}:
  match d:
    case Wr.Got{h, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.ev_commit(d: Wr.Dec<Tl.Next>) -> {FTl.get_ev.commit(d) == SpW.r_ev.commit(d) : Wr.Dec<Tl.Ev>}:
  match d:
    case Wr.Got{n, s}:
      ter.ev_commit_h(n, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ter.ev_settle_h(o: Tl.Outcome, d: Wr.Dec<Bool>) -> {FTl.get_ev.settle_h(o, d) == SpW.r_ev.settle_h(o, d) : Wr.Dec<Tl.Ev>}:
  match d:
    case Wr.Got{h, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.ev_settle(d: Wr.Dec<Tl.Outcome>) -> {FTl.get_ev.settle(d) == SpW.r_ev.settle(d) : Wr.Dec<Tl.Ev>}:
  match d:
    case Wr.Got{o, s}:
      ter.ev_settle_h(o, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ter.ev_fin(d: Wr.Dec<Bool>) -> {FTl.get_ev.fin(d) == SpW.r_ev.fin(d) : Wr.Dec<Tl.Ev>}:
  match d:
    case Wr.Got{h, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.ev(d: Wr.Dec<Nat>) -> {FTl.get_ev(d) == SpW.r_ev(d) : Wr.Dec<Tl.Ev>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          {==}
        case 1n:
          %ter.next(Wr.get_nat(s)) : {FTl.get_ev.commit(FTl.get_next(Wr.get_nat(s))) == SpW.r_ev.commit(_) : Wr.Dec<Tl.Ev>}
          ter.ev_commit(FTl.get_next(Wr.get_nat(s)))
        case 2n:
          {==}
        case 3n:
          %ter.out2(Wr.get_nat(s)) : {FTl.get_ev.settle(FTl.get_outcome(FTl.get_res(Wr.get_nat(s)))) == SpW.r_ev.settle(_) : Wr.Dec<Tl.Ev>}
          ter.ev_settle(FTl.get_outcome(FTl.get_res(Wr.get_nat(s))))
        case 4n:
          ter.ev_fin(Wr.get_bool(s))
        case 5n+u:
          {==}
    case Wr.Bad{}:
      {==}

# Rows
# ----

def ter.row_mark(l: Bool, b: Bool, d: Wr.Dec<Tl.Mark>) -> {FTl.get_row.mark(l, b, d) == SpW.r_row.mark(l, b, d) : Wr.Dec<Tl.Row>}:
  match d:
    case Wr.Got{m, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.row_bg(l: Bool, d: Wr.Dec<Bool>) -> {FTl.get_row.bg(l, d) == SpW.r_row.bg(l, d) : Wr.Dec<Tl.Row>}:
  match d:
    case Wr.Got{+b, +s}:
      %ter.mark(Wr.get_nat(s)) : {FTl.get_row.mark(l, b, FTl.get_mark(Wr.get_nat(s))) == SpW.r_row.mark(l, b, _) : Wr.Dec<Tl.Row>}
      ter.row_mark(l, b, FTl.get_mark(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def ter.row_live(d: Wr.Dec<Bool>) -> {FTl.get_row.live(d) == SpW.r_row.live(d) : Wr.Dec<Tl.Row>}:
  match d:
    case Wr.Got{l, s}:
      ter.row_bg(l, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ter.row(s: String) -> {FTl.get_row(s) == SpW.r_row(s) : Wr.Dec<Tl.Row>}:
  ter.row_live(Wr.get_bool(s))

# the item loops read the same rows
def ter.list_go(n: Nat, cur: Wr.Dec<Tl.Row>) -> {Wr.get_list.go(~Tl.Row, ~FTl.get_row, n, cur) == Wr.get_list.go(~Tl.Row, ~SpW.r_row, n, cur) : Wr.Dec<List<&2, Tl.Row>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %ter.row(s) : {Wr.get_list.cons(Tl.Row, x, Wr.get_list.go(~Tl.Row, ~FTl.get_row, m, FTl.get_row(s))) == Wr.get_list.cons(Tl.Row, x, Wr.get_list.go(~Tl.Row, ~SpW.r_row, m, _)) : Wr.Dec<List<&2, Tl.Row>>}
          %ter.list_go(m, FTl.get_row(s)) : {Wr.get_list.cons(Tl.Row, x, Wr.get_list.go(~Tl.Row, ~FTl.get_row, m, FTl.get_row(s))) == Wr.get_list.cons(Tl.Row, x, _) : Wr.Dec<List<&2, Tl.Row>>}
          {==}
        case Wr.Bad{}:
          {==}

def ter.list_start(d: Wr.Dec<Nat>) -> {Wr.get_list.start(~Tl.Row, ~FTl.get_row, d) == Wr.get_list.start(~Tl.Row, ~SpW.r_row, d) : Wr.Dec<List<&2, Tl.Row>>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %ter.row(s) : {Wr.get_list.go(~Tl.Row, ~FTl.get_row, m, FTl.get_row(s)) == Wr.get_list.go(~Tl.Row, ~SpW.r_row, m, _) : Wr.Dec<List<&2, Tl.Row>>}
          ter.list_go(m, FTl.get_row(s))
    case Wr.Bad{}:
      {==}

def ter.list(s: String) -> {Wr.get_list(~Tl.Row, ~FTl.get_row, s) == Wr.get_list(~Tl.Row, ~SpW.r_row, s) : Wr.Dec<List<&2, Tl.Row>>}:
  ter.list_start(Wr.get_nat(s))

# Requests
# --------

def ter.step_e(x: Tl.St, d: Wr.Dec<Tl.Ev>) -> {FTl.get_req.step_e(x, d) == SpW.r_req.step_e(x, d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{e, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.step(d: Wr.Dec<Tl.St>) -> {FTl.get_req.step(d) == SpW.r_req.step(d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{+x, +s}:
      %ter.ev(Wr.get_nat(s)) : {FTl.get_req.step_e(x, FTl.get_ev(Wr.get_nat(s))) == SpW.r_req.step_e(x, _) : Wr.Dec<FTl.Req>}
      ter.step_e(x, FTl.get_ev(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def ter.resume(d: Wr.Dec<Tl.St>) -> {FTl.get_req.resume(d) == SpW.r_req.resume(d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.join_f(p: Tl.Policy, ls: List<&2, Bool>, d: Wr.Dec<List<&2, Bool>>) -> {FTl.get_req.join_f(p, ls, d) == SpW.r_req.join_f(p, ls, d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{fs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.join_l(p: Tl.Policy, d: Wr.Dec<List<&2, Bool>>) -> {FTl.get_req.join_l(p, d) == SpW.r_req.join_l(p, d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{ls, s}:
      ter.join_f(p, ls, Wr.get_list(~Bool, ~Wr.get_bool, s))
    case Wr.Bad{}:
      {==}

def ter.join(d: Wr.Dec<Tl.Policy>) -> {FTl.get_req.join(d) == SpW.r_req.join(d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{p, s}:
      ter.join_l(p, Wr.get_list(~Bool, ~Wr.get_bool, s))
    case Wr.Bad{}:
      {==}

def ter.merge_b(a: Tl.Mark, d: Wr.Dec<Tl.Mark>) -> {FTl.get_req.merge_b(a, d) == SpW.r_req.merge_b(a, d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.merge(d: Wr.Dec<Tl.Mark>) -> {FTl.get_req.merge(d) == SpW.r_req.merge(d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{+a, +s}:
      %ter.mark(Wr.get_nat(s)) : {FTl.get_req.merge_b(a, FTl.get_mark(Wr.get_nat(s))) == SpW.r_req.merge_b(a, _) : Wr.Dec<FTl.Req>}
      ter.merge_b(a, FTl.get_mark(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def ter.cascade_r(x: Tl.St, m: Tl.Mark, d: Wr.Dec<List<&2, Tl.Row>>) -> {FTl.get_req.cascade_r(x, m, d) == SpW.r_req.cascade_r(x, m, d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{rs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ter.cascade_m(x: Tl.St, d: Wr.Dec<Tl.Mark>) -> {FTl.get_req.cascade_m(x, d) == SpW.r_req.cascade_m(x, d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{+m, +s}:
      %ter.list(s) : {FTl.get_req.cascade_r(x, m, Wr.get_list(~Tl.Row, ~FTl.get_row, s)) == SpW.r_req.cascade_r(x, m, _) : Wr.Dec<FTl.Req>}
      ter.cascade_r(x, m, Wr.get_list(~Tl.Row, ~FTl.get_row, s))
    case Wr.Bad{}:
      {==}

def ter.cascade(d: Wr.Dec<Tl.St>) -> {FTl.get_req.cascade(d) == SpW.r_req.cascade(d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{+x, +s}:
      %ter.mark(Wr.get_nat(s)) : {FTl.get_req.cascade_m(x, FTl.get_mark(Wr.get_nat(s))) == SpW.r_req.cascade_m(x, _) : Wr.Dec<FTl.Req>}
      ter.cascade_m(x, FTl.get_mark(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

# the entry's decoder is the laws' reader
def ter.req(d: Wr.Dec<Nat>) -> {FTl.get_req(d) == SpW.r_req(d) : Wr.Dec<FTl.Req>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          %ter.st(Wr.get_nat(s)) : {FTl.get_req.step(FTl.get_st(Wr.get_nat(s))) == SpW.r_req.step(_) : Wr.Dec<FTl.Req>}
          ter.step(FTl.get_st(Wr.get_nat(s)))
        case 1n:
          %ter.st(Wr.get_nat(s)) : {FTl.get_req.resume(FTl.get_st(Wr.get_nat(s))) == SpW.r_req.resume(_) : Wr.Dec<FTl.Req>}
          ter.resume(FTl.get_st(Wr.get_nat(s)))
        case 2n:
          %ter.policy(Wr.get_nat(s)) : {FTl.get_req.join(FTl.get_policy(Wr.get_nat(s))) == SpW.r_req.join(_) : Wr.Dec<FTl.Req>}
          ter.join(FTl.get_policy(Wr.get_nat(s)))
        case 3n:
          %ter.mark(Wr.get_nat(s)) : {FTl.get_req.merge(FTl.get_mark(Wr.get_nat(s))) == SpW.r_req.merge(_) : Wr.Dec<FTl.Req>}
          ter.merge(FTl.get_mark(Wr.get_nat(s)))
        case 4n:
          %ter.st(Wr.get_nat(s)) : {FTl.get_req.cascade(FTl.get_st(Wr.get_nat(s))) == SpW.r_req.cascade(_) : Wr.Dec<FTl.Req>}
          ter.cascade(FTl.get_st(Wr.get_nat(s)))
        case 5n+u:
          {==}
    case Wr.Bad{}:
      {==}
