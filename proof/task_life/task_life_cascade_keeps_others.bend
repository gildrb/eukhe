# eukhe: the proof of LAW task_life_cascade_keeps_others
#
# PROOF: by induction on the reached tasks: the row at i is not a live
# foreground task (the premise), so whatever the owner's intent the
# cascade keeps its mark (tlc.row_keep, case on the row's flags); past
# the last row both sides are None.

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def tlc.row_keep(go: Bool, by: Tl.Mark, r: Tl.Row, idle: {Sp.row_hit(r) == False{} : Bool}) -> {Some{Tl.cascade.row(go, by, r)} == Sp.row_mark(Some{r}) : Maybe<&2, Tl.Mark>}:
  match go:
    case True{}:
      match r:
        case Tl.Row{l, b, k}:
          match l:
            case True{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  LB.tlb.absurd_tf({Some{Tl.cascade.row(True{}, by, Tl.Row{True{}, False{}, k})} == Some{k} : Maybe<&2, Tl.Mark>}, idle)
            case False{}:
              {==}
    case False{}:
      match r:
        case Tl.Row{l, b, k}:
          {==}

def tlc.keep(+go: Bool, +by: Tl.Mark, rs: List<&2, Tl.Row>, i: Nat, idle: {Sp.hit_at(rs, i) == False{} : Bool}) -> {List.get(&2, Tl.Mark, Tl.cascade.rows(go, by, rs), i) == Sp.row_mark(List.get(&2, Tl.Row, rs, i)) : Maybe<&2, Tl.Mark>}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      match i:
        case 0n:
          tlc.row_keep(go, by, r, idle)
        case 1n+p:
          tlc.keep(go, by, t, p, idle)

def TaskLife.task_life_cascade_keeps_others(s, m, rs, i, idle):
  tlc.keep(Tl.intent(s, m), Tl.reason(s, m), rs, i, idle)
