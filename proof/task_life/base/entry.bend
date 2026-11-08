# eukhe: lemmas of the entry proofs of area task_life: a spelled request
# reads back with the rest untouched (tle.*: wire_nat_round_trip for the
# handles, the Bool-list round trip of area log for the join's flags, a
# round trip of the cascade's rows written here), and the reply encoders
# are the spec spellers (tlr.*)

import Base
import ../../../bend/task_life.bend as Tl
import ../../../bend/ffi_task_life.bend as FTl
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../spec/durable/task_life_wire.bend as SpW
import ../../base/wire.bend as LWire
import ../../log/base.bend as LLog
import ../../base/logic/bool.bend as LLogicBool

# Round trips: the value, then the rest, reads back from its spelling
# -------------------------------------------------------------------

def tle.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def tle.bools(+xs: List<&2, Bool>, +rest: String, h: {LawsBase.wire_fits(List.length(&2, Bool, xs)) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Bool, ~Wr.get_bool, SpW.w_bools(xs, rest)) : Wr.Dec<List<&2, Bool>>}:
  Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_list(~Bool, ~Wr.put_bool, xs, rest)), Wr.Got{xs, rest}, LLog.pe.rt(xs, rest, h))

def tle.policy(p: Tl.Policy, rest: String) -> {Wr.Got{p, rest} == FTl.get_policy(Wr.get_nat(SpW.w_policy(p, rest))) : Wr.Dec<Tl.Policy>}:
  match p:
    case Tl.FailFast{}:
      {==}
    case Tl.AllSettled{}:
      {==}

def tle.res(x: Tl.Res, rest: String) -> {Wr.Got{x, rest} == FTl.get_res(Wr.get_nat(Wr.put_nat(SpW.w_res(x), rest))) : Wr.Dec<Tl.Res>}:
  match x:
    case Tl.RCompleted{}:
      {==}
    case Tl.RFailed{}:
      {==}
    case Tl.RAborted{}:
      {==}
    case Tl.ROrphaned{}:
      {==}
    case Tl.RFaulted{}:
      {==}

def tle.mark(m: Tl.Mark, rest: String) -> {Wr.Got{m, rest} == FTl.get_mark(Wr.get_nat(SpW.w_mark(m, rest))) : Wr.Dec<Tl.Mark>}:
  match m:
    case Tl.Clear{}:
      {==}
    case Tl.Restart{}:
      {==}
    case Tl.Request{}:
      {==}

def tle.outcome(o: Tl.Outcome, +rest: String, h: {SpW.fit_outcome(o) == True{} : Bool}) -> {Wr.Got{o, rest} == FTl.get_outcome(FTl.get_res(Wr.get_nat(SpW.w_outcome(o, rest)))) : Wr.Dec<Tl.Outcome>}:
  match o:
    case Tl.Outcome{+x, +k}:
      %tle.res(x, Wr.put_nat(k, rest)) : {Wr.Got{Tl.Outcome{x, k}, rest} == FTl.get_outcome(_) : Wr.Dec<Tl.Outcome>}
      %tle.nat(k, rest, h) : {Wr.Got{Tl.Outcome{x, k}, rest} == FTl.get_outcome.h(x, _) : Wr.Dec<Tl.Outcome>}
      {==}

def tle.st(x: Tl.St, +rest: String, h: {SpW.fit_st(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FTl.get_st(Wr.get_nat(SpW.w_st(x, rest))) : Wr.Dec<Tl.St>}:
  match x:
    case Tl.Pending{+c}:
      %tle.nat(c, rest, h) : {Wr.Got{Tl.Pending{c}, rest} == FTl.get_st.one(_, 0n) : Wr.Dec<Tl.St>}
      {==}
    case Tl.Running{+c}:
      %tle.nat(c, rest, h) : {Wr.Got{Tl.Running{c}, rest} == FTl.get_st.one(_, 1n) : Wr.Dec<Tl.St>}
      {==}
    case Tl.Waiting{+c, +p}:
      %tle.nat(c, SpW.w_policy(p, rest), h) : {Wr.Got{Tl.Waiting{c, p}, rest} == FTl.get_st.wait(_) : Wr.Dec<Tl.St>}
      %tle.policy(p, rest) : {Wr.Got{Tl.Waiting{c, p}, rest} == FTl.get_st.policy(c, _) : Wr.Dec<Tl.St>}
      {==}
    case Tl.Completing{+o}:
      %tle.outcome(o, rest, h) : {Wr.Got{Tl.Completing{o}, rest} == FTl.get_st.out(_, 0n) : Wr.Dec<Tl.St>}
      {==}
    case Tl.Terminal{+o}:
      %tle.outcome(o, rest, h) : {Wr.Got{Tl.Terminal{o}, rest} == FTl.get_st.out(_, 1n) : Wr.Dec<Tl.St>}
      {==}

def tle.next(n: Tl.Next, +rest: String, h: {SpW.fit_next(n) == True{} : Bool}) -> {Wr.Got{n, rest} == FTl.get_next(Wr.get_nat(SpW.w_next(n, rest))) : Wr.Dec<Tl.Next>}:
  match n:
    case Tl.NRun{+c}:
      %tle.nat(c, rest, h) : {Wr.Got{Tl.NRun{c}, rest} == FTl.get_next.run(_) : Wr.Dec<Tl.Next>}
      {==}
    case Tl.NWait{+c, +p}:
      %tle.nat(c, SpW.w_policy(p, rest), h) : {Wr.Got{Tl.NWait{c, p}, rest} == FTl.get_next.wait(_) : Wr.Dec<Tl.Next>}
      %tle.policy(p, rest) : {Wr.Got{Tl.NWait{c, p}, rest} == FTl.get_next.policy(c, _) : Wr.Dec<Tl.Next>}
      {==}
    case Tl.NEnd{+o}:
      %tle.outcome(o, rest, h) : {Wr.Got{Tl.NEnd{o}, rest} == FTl.get_next.end(_) : Wr.Dec<Tl.Next>}
      {==}

def tle.ev(e: Tl.Ev, +rest: String, h: {SpW.fit_ev(e) == True{} : Bool}) -> {Wr.Got{e, rest} == FTl.get_ev(Wr.get_nat(SpW.w_ev(e, rest))) : Wr.Dec<Tl.Ev>}:
  match e:
    case Tl.Reserve{}:
      {==}
    case Tl.Commit{+n, b}:
      match b:
        case True{}:
          %tle.next(n, Wr.put_bool(True{}, rest), h) : {Wr.Got{Tl.Commit{n, True{}}, rest} == FTl.get_ev.commit(_) : Wr.Dec<Tl.Ev>}
          {==}
        case False{}:
          %tle.next(n, Wr.put_bool(False{}, rest), h) : {Wr.Got{Tl.Commit{n, False{}}, rest} == FTl.get_ev.commit(_) : Wr.Dec<Tl.Ev>}
          {==}
    case Tl.Requeue{}:
      {==}
    case Tl.Settle{+o, b}:
      match b:
        case True{}:
          %tle.outcome(o, Wr.put_bool(True{}, rest), h) : {Wr.Got{Tl.Settle{o, True{}}, rest} == FTl.get_ev.settle(_) : Wr.Dec<Tl.Ev>}
          {==}
        case False{}:
          %tle.outcome(o, Wr.put_bool(False{}, rest), h) : {Wr.Got{Tl.Settle{o, False{}}, rest} == FTl.get_ev.settle(_) : Wr.Dec<Tl.Ev>}
          {==}
    case Tl.Finalize{b}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

# Rows
# ----

# the items of a list of rows, then rest
def tle.items(rs: List<&2, Tl.Row>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case r <> t:
      SpW.w_row(r, tle.items(t, rest))

def tle.put_go(rs: List<&2, Tl.Row>, -rest: String) -> {Wr.put_list.go(~Tl.Row, ~SpW.w_row, rs, rest) == (List.length(&2, Tl.Row, rs), tle.items(rs, rest)) : Nat & String}:
  match rs:
    case Nil{}:
      {==}
    case Con{r, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Tl.Row, ~SpW.w_row, t, rest), (List.length(&2, Tl.Row, t), tle.items(t, rest)), tle.put_go(t, rest)) : {Wr.put_list.step(~Tl.Row, ~SpW.w_row, r, _) == (1n+List.length(&2, Tl.Row, t), SpW.w_row(r, tle.items(t, rest))) : Nat & String}
      {==}

def tle.put_rows(+rs: List<&2, Tl.Row>, -rest: String) -> {Wr.put_list(~Tl.Row, ~SpW.w_row, rs, rest) == Wr.put_nat(List.length(&2, Tl.Row, rs), tle.items(rs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Tl.Row, ~SpW.w_row, rs, rest), (List.length(&2, Tl.Row, rs), tle.items(rs, rest)), tle.put_go(rs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Tl.Row, rs), tle.items(rs, rest)) : String}
  {==}

# a spelled row reads back
def tle.row(r: Tl.Row, rest: String) -> {FTl.get_row(SpW.w_row(r, rest)) == Wr.Got{r, rest} : Wr.Dec<Tl.Row>}:
  match r:
    case Tl.Row{l, b, m}:
      match l:
        case True{}:
          match b:
            case True{}:
              match m:
                case Tl.Clear{}:
                  {==}
                case Tl.Restart{}:
                  {==}
                case Tl.Request{}:
                  {==}
            case False{}:
              match m:
                case Tl.Clear{}:
                  {==}
                case Tl.Restart{}:
                  {==}
                case Tl.Request{}:
                  {==}
        case False{}:
          match b:
            case True{}:
              match m:
                case Tl.Clear{}:
                  {==}
                case Tl.Restart{}:
                  {==}
                case Tl.Request{}:
                  {==}
            case False{}:
              match m:
                case Tl.Clear{}:
                  {==}
                case Tl.Restart{}:
                  {==}
                case Tl.Request{}:
                  {==}

# the item loop reads back x, then t
def tle.go_rt(+t: List<&2, Tl.Row>, +x: Tl.Row, +rest: String) -> {Wr.get_list.go(~Tl.Row, ~FTl.get_row, List.length(&2, Tl.Row, t), FTl.get_row(SpW.w_row(x, tle.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Tl.Row>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Tl.Row>, FTl.get_row(SpW.w_row(x, rest)), Wr.Got{x, rest}, tle.row(x, rest)) : {Wr.get_list.go(~Tl.Row, ~FTl.get_row, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Tl.Row>>}
      {==}
    case +y <> +u:
      +r2 = SpW.w_row(y, tle.items(u, rest))
      %Equal.sym(Wr.Dec<Tl.Row>, FTl.get_row(SpW.w_row(x, r2)), Wr.Got{x, r2}, tle.row(x, r2)) : {Wr.get_list.go(~Tl.Row, ~FTl.get_row, 1n+List.length(&2, Tl.Row, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Tl.Row>>}
      %Equal.sym(Wr.Dec<List<&2, Tl.Row>>, Wr.get_list.go(~Tl.Row, ~FTl.get_row, List.length(&2, Tl.Row, u), FTl.get_row(r2)), Wr.Got{y <> u, rest}, tle.go_rt(u, y, rest)) : {Wr.get_list.cons(Tl.Row, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Tl.Row>>}
      {==}

# a list of rows whose count fits reads back
def tle.rows(rs: List<&2, Tl.Row>, +rest: String, h: {LawsBase.wire_fits(List.length(&2, Tl.Row, rs)) == True{} : Bool}) -> {Wr.Got{rs, rest} == Wr.get_list(~Tl.Row, ~FTl.get_row, Wr.put_list(~Tl.Row, ~SpW.w_row, rs, rest)) : Wr.Dec<List<&2, Tl.Row>>}:
  match rs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(String, Wr.put_list(~Tl.Row, ~SpW.w_row, x <> t, rest), Wr.put_nat(1n+List.length(&2, Tl.Row, t), tle.items(x <> t, rest)), tle.put_rows(x <> t, rest)) : {Wr.Got{x <> t, rest} == Wr.get_list(~Tl.Row, ~FTl.get_row, _) : Wr.Dec<List<&2, Tl.Row>>}
      %tle.nat(1n+List.length(&2, Tl.Row, t), tle.items(x <> t, rest), h) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~Tl.Row, ~FTl.get_row, _) : Wr.Dec<List<&2, Tl.Row>>}
      Equal.sym(Wr.Dec<List<&2, Tl.Row>>, Wr.get_list.go(~Tl.Row, ~FTl.get_row, List.length(&2, Tl.Row, t), FTl.get_row(SpW.w_row(x, tle.items(t, rest)))), Wr.Got{x <> t, rest}, tle.go_rt(t, x, rest))

# Requests
# --------

# a spelled request that fits reads back, and the rest is untouched
def tle.req(q: FTl.Req, +rest: String, h: {SpW.fit_req(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FTl.get_req(Wr.get_nat(SpW.w_req(q, rest))) : Wr.Dec<FTl.Req>}:
  match q:
    case FTl.QStep{+x, +e}:
      +hq = h
      +hx = LLogicBool.tree.pt.and_l(SpW.fit_st(x), SpW.fit_ev(e), hq)
      +he = LLogicBool.tree.pt.and_r(SpW.fit_st(x), SpW.fit_ev(e), hq)
      %tle.st(x, SpW.w_ev(e, rest), hx) : {Wr.Got{FTl.QStep{x, e}, rest} == FTl.get_req.step(_) : Wr.Dec<FTl.Req>}
      %tle.ev(e, rest, he) : {Wr.Got{FTl.QStep{x, e}, rest} == FTl.get_req.step_e(x, _) : Wr.Dec<FTl.Req>}
      {==}
    case FTl.QResume{+x}:
      %tle.st(x, rest, h) : {Wr.Got{FTl.QResume{x}, rest} == FTl.get_req.resume(_) : Wr.Dec<FTl.Req>}
      {==}
    case FTl.QJoin{+p, +ls, +fs}:
      +hq = h
      +hl = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(List.length(&2, Bool, ls)), LawsBase.wire_fits(List.length(&2, Bool, fs)), hq)
      +hf = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(List.length(&2, Bool, ls)), LawsBase.wire_fits(List.length(&2, Bool, fs)), hq)
      %tle.policy(p, SpW.w_bools(ls, SpW.w_bools(fs, rest))) : {Wr.Got{FTl.QJoin{p, ls, fs}, rest} == FTl.get_req.join(_) : Wr.Dec<FTl.Req>}
      %tle.bools(ls, SpW.w_bools(fs, rest), hl) : {Wr.Got{FTl.QJoin{p, ls, fs}, rest} == FTl.get_req.join_l(p, _) : Wr.Dec<FTl.Req>}
      %tle.bools(fs, rest, hf) : {Wr.Got{FTl.QJoin{p, ls, fs}, rest} == FTl.get_req.join_f(p, ls, _) : Wr.Dec<FTl.Req>}
      {==}
    case FTl.QMerge{+a, +b}:
      %tle.mark(a, SpW.w_mark(b, rest)) : {Wr.Got{FTl.QMerge{a, b}, rest} == FTl.get_req.merge(_) : Wr.Dec<FTl.Req>}
      %tle.mark(b, rest) : {Wr.Got{FTl.QMerge{a, b}, rest} == FTl.get_req.merge_b(a, _) : Wr.Dec<FTl.Req>}
      {==}
    case FTl.QCascade{+x, +m, +rs}:
      +hq = h
      +hx = LLogicBool.tree.pt.and_l(SpW.fit_st(x), LawsBase.wire_fits(List.length(&2, Tl.Row, rs)), hq)
      +hr = LLogicBool.tree.pt.and_r(SpW.fit_st(x), LawsBase.wire_fits(List.length(&2, Tl.Row, rs)), hq)
      +l = Wr.put_list(~Tl.Row, ~SpW.w_row, rs, rest)
      %tle.st(x, SpW.w_mark(m, l), hx) : {Wr.Got{FTl.QCascade{x, m, rs}, rest} == FTl.get_req.cascade(_) : Wr.Dec<FTl.Req>}
      %tle.mark(m, l) : {Wr.Got{FTl.QCascade{x, m, rs}, rest} == FTl.get_req.cascade_m(x, _) : Wr.Dec<FTl.Req>}
      %tle.rows(rs, rest, hr) : {Wr.Got{FTl.QCascade{x, m, rs}, rest} == FTl.get_req.cascade_r(x, m, _) : Wr.Dec<FTl.Req>}
      {==}

# Replies: the encoders are the spec spellers
# ------------------------------------------

def tlr.st(x: Tl.St, rest: String) -> {FTl.put_st(x, rest) == SpW.w_st(x, rest) : String}:
  match x:
    case Tl.Pending{c}:
      {==}
    case Tl.Running{c}:
      {==}
    case Tl.Waiting{c, p}:
      match p:
        case Tl.FailFast{}:
          {==}
        case Tl.AllSettled{}:
          {==}
    case Tl.Completing{o}:
      match o:
        case Tl.Outcome{r, k}:
          match r:
            case Tl.RCompleted{}:
              {==}
            case Tl.RFailed{}:
              {==}
            case Tl.RAborted{}:
              {==}
            case Tl.ROrphaned{}:
              {==}
            case Tl.RFaulted{}:
              {==}
    case Tl.Terminal{o}:
      match o:
        case Tl.Outcome{r, k}:
          match r:
            case Tl.RCompleted{}:
              {==}
            case Tl.RFailed{}:
              {==}
            case Tl.RAborted{}:
              {==}
            case Tl.ROrphaned{}:
              {==}
            case Tl.RFaulted{}:
              {==}

def tlr.stepped(r: Result<&2, &2, Tl.Why, Tl.St>) -> {FTl.put_stepped(r) == SpW.w_stepped(r) : String}:
  match r:
    case Fail{y}:
      match y:
        case Tl.Ended{}:
          {==}
        case Tl.Held{}:
          {==}
        case Tl.NotRunning{}:
          {==}
        case Tl.NotHeld{}:
          {==}
    case Done{+x}:
      %tlr.st(x, "") : {Wr.put_nat(1n, FTl.put_st(x, "")) == Wr.put_nat(1n, _) : String}
      {==}

def tlr.resumed(r: Tl.St & Bool) -> {FTl.put_resumed(r) == SpW.w_resumed(r) : String}:
  (+x, +b) = r
  %tlr.st(x, Wr.put_bool(b, "")) : {FTl.put_st(x, Wr.put_bool(b, "")) == _ : String}
  {==}

def tlr.joined(r: Bool & List<&2, Bool>) -> {FTl.put_joined(r) == SpW.w_joined(r) : String}:
  (ok, ms) = r
  {==}

def tlr.mark(m: Tl.Mark, rest: String) -> {FTl.put_mark(m, rest) == SpW.w_mark(m, rest) : String}:
  match m:
    case Tl.Clear{}:
      {==}
    case Tl.Restart{}:
      {==}
    case Tl.Request{}:
      {==}

def tlr.mstep(m: Tl.Mark, g: Nat & String) -> {Wr.put_list.step(~Tl.Mark, ~FTl.put_mark, m, g) == Wr.put_list.step(~Tl.Mark, ~SpW.w_mark, m, g) : Nat & String}:
  match m:
    case Tl.Clear{}:
      (n, s) = g
      {==}
    case Tl.Restart{}:
      (n, s) = g
      {==}
    case Tl.Request{}:
      (n, s) = g
      {==}

def tlr.marks_go(ms: List<&2, Tl.Mark>, +rest: String) -> {Wr.put_list.go(~Tl.Mark, ~FTl.put_mark, ms, rest) == Wr.put_list.go(~Tl.Mark, ~SpW.w_mark, ms, rest) : Nat & String}:
  match ms:
    case Nil{}:
      {==}
    case +m <> +t:
      %tlr.marks_go(t, rest) : {Wr.put_list.step(~Tl.Mark, ~FTl.put_mark, m, Wr.put_list.go(~Tl.Mark, ~FTl.put_mark, t, rest)) == Wr.put_list.step(~Tl.Mark, ~SpW.w_mark, m, _) : Nat & String}
      tlr.mstep(m, Wr.put_list.go(~Tl.Mark, ~FTl.put_mark, t, rest))

# the reply of a request is the spec's spelling of the rules' decision
def tlr.answer(q: FTl.Req) -> {FTl.answer(q) == SpW.w_reply(q) : String}:
  match q:
    case FTl.QStep{x, e}:
      tlr.stepped(Tl.step(x, e))
    case FTl.QResume{x}:
      tlr.resumed(Tl.resume(x))
    case FTl.QJoin{p, ls, fs}:
      tlr.joined(Tl.join(p, ls, fs))
    case FTl.QMerge{a, b}:
      tlr.mark(Tl.merge(a, b), "")
    case FTl.QCascade{x, m, rs}:
      +ms = Tl.cascade(x, m, rs)
      %tlr.marks_go(ms, "") : {Wr.put_list.fin(Wr.put_list.go(~Tl.Mark, ~FTl.put_mark, ms, "")) == Wr.put_list.fin(_) : String}
      {==}
