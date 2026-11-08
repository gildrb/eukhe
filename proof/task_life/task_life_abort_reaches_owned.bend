# eukhe: the proof of LAW task_life_abort_reaches_owned
#
# PROOF: the owner's intent and reason are the spec's (tlb.intent,
# tlb.reason); then row by row: a reached task is marked exactly when the
# spec marks it, with the spec's merge (task_life_mark_merge).

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/submission.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB
import ./task_life_mark_merge.bend as PTaskLifeMarkMerge

def tla.pick(+hit: Bool, +m: Tl.Mark, +by: Tl.Mark) -> {Tl.cascade.pick(hit, m, by) == Sp.pick_mark(hit, Sp.merge_spec(m, by), m) : Tl.Mark}:
  match hit:
    case True{}:
      TaskLife.task_life_mark_merge(m, by)
    case False{}:
      {==}

def tla.rows(+go: Bool, +by: Tl.Mark, rs: List<&2, Tl.Row>) -> {Tl.cascade.rows(go, by, rs) == Sp.cascade_rows_spec(go, by, rs) : List<&2, Tl.Mark>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Tl.Row{+l, +b, +m}:
          +hit = Bool.and(go, Bool.and(l, Bool.not(b)))
          %tla.pick(hit, m, by) : {Tl.cascade.pick(hit, m, by) <> Tl.cascade.rows(go, by, t) == _ <> Sp.cascade_rows_spec(go, by, t) : List<&2, Tl.Mark>}
          %tla.rows(go, by, t) : {Tl.cascade.pick(hit, m, by) <> Tl.cascade.rows(go, by, t) == Tl.cascade.pick(hit, m, by) <> _ : List<&2, Tl.Mark>}
          {==}

def TaskLife.task_life_abort_reaches_owned(s, m, rs):
  %LB.tlb.intent(s, m) : {Tl.cascade(s, m, rs) == Sp.cascade_rows_spec(_, Sp.reason_spec(s, m), rs) : List<&2, Tl.Mark>}
  %LB.tlb.reason(s, m) : {Tl.cascade(s, m, rs) == Sp.cascade_rows_spec(Tl.intent(s, m), _, rs) : List<&2, Tl.Mark>}
  tla.rows(Tl.intent(s, m), Tl.reason(s, m), rs)
