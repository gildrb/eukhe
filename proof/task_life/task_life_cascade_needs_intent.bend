# eukhe: the proof of LAW task_life_cascade_needs_intent
#
# PROOF: case on the owner and its mark: a terminal owner, or a live one
# with no mark and no failed outcome, has no intent (it computes); every
# other case contradicts the premise calm. With no intent every row keeps
# its mark (tlc.quiet, by induction).

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def tlc.quiet(+by: Tl.Mark, rs: List<&2, Tl.Row>) -> {Tl.cascade.rows(False{}, by, rs) == Sp.own_marks(rs) : List<&2, Tl.Mark>}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case Tl.Row{l, b, k}:
          %tlc.quiet(by, t) : {k <> Tl.cascade.rows(False{}, by, t) == k <> _ : List<&2, Tl.Mark>}
          {==}

def tlc.NG(+s: Tl.St, +m: Tl.Mark, +rs: List<&2, Tl.Row>) -> Type:
  {Tl.cascade(s, m, rs) == Sp.own_marks(rs) : List<&2, Tl.Mark>}

def tlc.calm_res(r: Tl.Res, +h: Nat, +rs: List<&2, Tl.Row>, calm: {Bool.or(False{}, Bool.and(True{}, Bool.not(Bool.not(Sp.res_ok(r))))) == True{} : Bool}) -> tlc.NG(Tl.Completing{Tl.Outcome{r, h}}, Tl.Clear{}, rs):
  match r:
    case Tl.RCompleted{}:
      tlc.quiet(Tl.Request{}, rs)
    case Tl.RFailed{}:
      LB.tlb.absurd_ft(tlc.NG(Tl.Completing{Tl.Outcome{Tl.RFailed{}, h}}, Tl.Clear{}, rs), calm)
    case Tl.RAborted{}:
      LB.tlb.absurd_ft(tlc.NG(Tl.Completing{Tl.Outcome{Tl.RAborted{}, h}}, Tl.Clear{}, rs), calm)
    case Tl.ROrphaned{}:
      LB.tlb.absurd_ft(tlc.NG(Tl.Completing{Tl.Outcome{Tl.ROrphaned{}, h}}, Tl.Clear{}, rs), calm)
    case Tl.RFaulted{}:
      LB.tlb.absurd_ft(tlc.NG(Tl.Completing{Tl.Outcome{Tl.RFaulted{}, h}}, Tl.Clear{}, rs), calm)

def TaskLife.task_life_cascade_needs_intent(s, m, rs, calm):
  match s:
    case Tl.Terminal{o}:
      tlc.quiet(Tl.reason(Tl.Terminal{o}, m), rs)
    case Tl.Pending{c}:
      match m:
        case Tl.Clear{}:
          tlc.quiet(Tl.Request{}, rs)
        case Tl.Restart{}:
          LB.tlb.absurd_ft(tlc.NG(Tl.Pending{c}, Tl.Restart{}, rs), calm)
        case Tl.Request{}:
          LB.tlb.absurd_ft(tlc.NG(Tl.Pending{c}, Tl.Request{}, rs), calm)
    case Tl.Running{c}:
      match m:
        case Tl.Clear{}:
          tlc.quiet(Tl.Request{}, rs)
        case Tl.Restart{}:
          LB.tlb.absurd_ft(tlc.NG(Tl.Running{c}, Tl.Restart{}, rs), calm)
        case Tl.Request{}:
          LB.tlb.absurd_ft(tlc.NG(Tl.Running{c}, Tl.Request{}, rs), calm)
    case Tl.Waiting{c, p}:
      match m:
        case Tl.Clear{}:
          tlc.quiet(Tl.Request{}, rs)
        case Tl.Restart{}:
          LB.tlb.absurd_ft(tlc.NG(Tl.Waiting{c, p}, Tl.Restart{}, rs), calm)
        case Tl.Request{}:
          LB.tlb.absurd_ft(tlc.NG(Tl.Waiting{c, p}, Tl.Request{}, rs), calm)
    case Tl.Completing{o}:
      match o:
        case Tl.Outcome{r, h}:
          match m:
            case Tl.Clear{}:
              tlc.calm_res(r, h, rs, calm)
            case Tl.Restart{}:
              LB.tlb.absurd_ft(tlc.NG(Tl.Completing{Tl.Outcome{r, h}}, Tl.Restart{}, rs), calm)
            case Tl.Request{}:
              LB.tlb.absurd_ft(tlc.NG(Tl.Completing{Tl.Outcome{r, h}}, Tl.Request{}, rs), calm)
