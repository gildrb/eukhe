# eukhe: the proof of LAW task_life_join_fail_fast_quiet
#
# PROOF: no failed flag counted means none is set (tlj.none_any, by
# induction), so failFast's marks are keep_all's, which count none
# (tlj.count_keep).

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB
import ./base/join.bend as LJ

def tlj.none_any(fs: List<&2, Bool>, e: {Sp.count(fs) == 0n : Nat}) -> {Tl.any(fs) == False{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case True{}:
          LB.tlb.succ_zero(Sp.count(t), {True{} == False{} : Bool}, e)
        case False{}:
          tlj.none_any(t, e)

def TaskLife.task_life_join_fail_fast_quiet(live, failed, none):
  %Equal.sym(Bool, Tl.any(failed), False{}, tlj.none_any(failed, none)) : {Sp.count(Tl.join.marks(Tl.FailFast{}, _, live, failed)) == 0n : Nat}
  LJ.tlj.count_keep(live)
