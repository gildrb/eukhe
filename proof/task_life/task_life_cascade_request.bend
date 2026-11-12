# eukhe: the proof of LAW task_life_cascade_request
#
# PROOF: case on the owner, its outcome and its mark: where the premises
# hold, the owner has intent and passes a request (it computes); the
# reached row i takes merge(k, request) (tlc.hit), which is a request
# for every k (tlc.req_merge). Every other case contradicts a premise.

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB
import ./base/cascade.bend as LC

def tlc.req_merge(k: Tl.Mark) -> {Tl.merge(k, Tl.Request{}) == Tl.Request{} : Tl.Mark}:
  match k:
    case Tl.Clear{}:
      {==}
    case Tl.Restart{}:
      {==}
    case Tl.Request{}:
      {==}

def tlc.RG(+s: Tl.St, +m: Tl.Mark, +rs: List<&2, Tl.Row>, +i: Nat) -> Type:
  {List.get(&2, Tl.Mark, Tl.cascade(s, m, rs), i) == Some{Tl.Request{}} : Maybe<&2, Tl.Mark>}

def tlc.req(+rs: List<&2, Tl.Row>, +i: Nat, +k: Tl.Mark, row: {List.get(&2, Tl.Row, rs, i) == Some{Tl.Row{True{}, False{}, k}} : Maybe<&2, Tl.Row>}) -> {List.get(&2, Tl.Mark, Tl.cascade.rows(True{}, Tl.Request{}, rs), i) == Some{Tl.Request{}} : Maybe<&2, Tl.Mark>}:
  %tlc.req_merge(k) : {List.get(&2, Tl.Mark, Tl.cascade.rows(True{}, Tl.Request{}, rs), i) == Some{_} : Maybe<&2, Tl.Mark>}
  LC.tlc.hit(Tl.Request{}, rs, i, k, row)

def tlc.req_res(r: Tl.Res, +h: Nat, +m: Tl.Mark, +rs: List<&2, Tl.Row>, +i: Nat, +k: Tl.Mark, row: {List.get(&2, Tl.Row, rs, i) == Some{Tl.Row{True{}, False{}, k}} : Maybe<&2, Tl.Row>}, why: {Bool.or(Nat.is_eq(Sp.mark_rank(m), 2n), Bool.not(Sp.res_ok(r))) == True{} : Bool}) -> tlc.RG(Tl.Completing{Tl.Outcome{r, h}}, m, rs, i):
  match r:
    case Tl.RCompleted{}:
      match m:
        case Tl.Request{}:
          tlc.req(rs, i, k, row)
        case Tl.Clear{}:
          LB.tlb.absurd_ft(tlc.RG(Tl.Completing{Tl.Outcome{Tl.RCompleted{}, h}}, Tl.Clear{}, rs, i), why)
        case Tl.Restart{}:
          LB.tlb.absurd_ft(tlc.RG(Tl.Completing{Tl.Outcome{Tl.RCompleted{}, h}}, Tl.Restart{}, rs, i), why)
    case Tl.RFailed{}:
      match m:
        case Tl.Clear{}:
          tlc.req(rs, i, k, row)
        case Tl.Restart{}:
          tlc.req(rs, i, k, row)
        case Tl.Request{}:
          tlc.req(rs, i, k, row)
    case Tl.RAborted{}:
      match m:
        case Tl.Clear{}:
          tlc.req(rs, i, k, row)
        case Tl.Restart{}:
          tlc.req(rs, i, k, row)
        case Tl.Request{}:
          tlc.req(rs, i, k, row)
    case Tl.ROrphaned{}:
      match m:
        case Tl.Clear{}:
          tlc.req(rs, i, k, row)
        case Tl.Restart{}:
          tlc.req(rs, i, k, row)
        case Tl.Request{}:
          tlc.req(rs, i, k, row)
    case Tl.RFaulted{}:
      match m:
        case Tl.Clear{}:
          tlc.req(rs, i, k, row)
        case Tl.Restart{}:
          tlc.req(rs, i, k, row)
        case Tl.Request{}:
          tlc.req(rs, i, k, row)

def TaskLife.task_life_cascade_request(s, m, rs, i, k, row, live, why):
  match s:
    case Tl.Pending{c}:
      match m:
        case Tl.Request{}:
          tlc.req(rs, i, k, row)
        case Tl.Clear{}:
          LB.tlb.absurd_ft(tlc.RG(Tl.Pending{c}, Tl.Clear{}, rs, i), why)
        case Tl.Restart{}:
          LB.tlb.absurd_ft(tlc.RG(Tl.Pending{c}, Tl.Restart{}, rs, i), why)
    case Tl.Running{c}:
      match m:
        case Tl.Request{}:
          tlc.req(rs, i, k, row)
        case Tl.Clear{}:
          LB.tlb.absurd_ft(tlc.RG(Tl.Running{c}, Tl.Clear{}, rs, i), why)
        case Tl.Restart{}:
          LB.tlb.absurd_ft(tlc.RG(Tl.Running{c}, Tl.Restart{}, rs, i), why)
    case Tl.Waiting{c, p}:
      match m:
        case Tl.Request{}:
          tlc.req(rs, i, k, row)
        case Tl.Clear{}:
          LB.tlb.absurd_ft(tlc.RG(Tl.Waiting{c, p}, Tl.Clear{}, rs, i), why)
        case Tl.Restart{}:
          LB.tlb.absurd_ft(tlc.RG(Tl.Waiting{c, p}, Tl.Restart{}, rs, i), why)
    case Tl.Completing{o}:
      match o:
        case Tl.Outcome{r, h}:
          tlc.req_res(r, h, m, rs, i, k, row, why)
    case Tl.Terminal{o}:
      LB.tlb.absurd_tf(tlc.RG(Tl.Terminal{o}, m, rs, i), live)
