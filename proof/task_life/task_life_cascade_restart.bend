# eukhe: the proof of LAW task_life_cascade_restart
#
# PROOF: case on the owner and its outcome: a live owner with the restart
# mark and no failed outcome has intent and passes restart (it computes);
# the reached row i takes merge(k, restart) (tlc.hit), which is
# merge_spec(k, restart) (tlc.restart_merge, case on k). A failed or
# terminal owner contradicts a premise.

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB
import ./base/cascade.bend as LC

def tlc.restart_merge(k: Tl.Mark) -> {Tl.merge(k, Tl.Restart{}) == Sp.merge_spec(k, Tl.Restart{}) : Tl.Mark}:
  match k:
    case Tl.Clear{}:
      {==}
    case Tl.Restart{}:
      {==}
    case Tl.Request{}:
      {==}

def tlc.SG(+s: Tl.St, +rs: List<&2, Tl.Row>, +i: Nat, +k: Tl.Mark) -> Type:
  {List.get(&2, Tl.Mark, Tl.cascade(s, Tl.Restart{}, rs), i) == Some{Sp.merge_spec(k, Tl.Restart{})} : Maybe<&2, Tl.Mark>}

def tlc.rst(+rs: List<&2, Tl.Row>, +i: Nat, +k: Tl.Mark, row: {List.get(&2, Tl.Row, rs, i) == Some{Tl.Row{True{}, False{}, k}} : Maybe<&2, Tl.Row>}) -> {List.get(&2, Tl.Mark, Tl.cascade.rows(True{}, Tl.Restart{}, rs), i) == Some{Sp.merge_spec(k, Tl.Restart{})} : Maybe<&2, Tl.Mark>}:
  %tlc.restart_merge(k) : {List.get(&2, Tl.Mark, Tl.cascade.rows(True{}, Tl.Restart{}, rs), i) == Some{_} : Maybe<&2, Tl.Mark>}
  LC.tlc.hit(Tl.Restart{}, rs, i, k, row)

def TaskLife.task_life_cascade_restart(s, rs, i, k, row, live, calm):
  match s:
    case Tl.Pending{c}:
      tlc.rst(rs, i, k, row)
    case Tl.Running{c}:
      tlc.rst(rs, i, k, row)
    case Tl.Waiting{c, p}:
      tlc.rst(rs, i, k, row)
    case Tl.Completing{o}:
      match o:
        case Tl.Outcome{r, h}:
          match r:
            case Tl.RCompleted{}:
              tlc.rst(rs, i, k, row)
            case Tl.RFailed{}:
              LB.tlb.absurd_tf(tlc.SG(Tl.Completing{Tl.Outcome{Tl.RFailed{}, h}}, rs, i, k), calm)
            case Tl.RAborted{}:
              LB.tlb.absurd_tf(tlc.SG(Tl.Completing{Tl.Outcome{Tl.RAborted{}, h}}, rs, i, k), calm)
            case Tl.ROrphaned{}:
              LB.tlb.absurd_tf(tlc.SG(Tl.Completing{Tl.Outcome{Tl.ROrphaned{}, h}}, rs, i, k), calm)
            case Tl.RFaulted{}:
              LB.tlb.absurd_tf(tlc.SG(Tl.Completing{Tl.Outcome{Tl.RFaulted{}, h}}, rs, i, k), calm)
    case Tl.Terminal{o}:
      LB.tlb.absurd_tf(tlc.SG(Tl.Terminal{o}, rs, i, k), live)
