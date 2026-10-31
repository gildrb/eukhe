# eukhe: the proof of LAW task_life_join_fail_fast
#
# PROOF: any is some (tlb.any) on both lists; then by whether some task
# failed: the marks of the rules are the spec's (tlb.ff_hit, tlb.ff_none).

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

def tlj.ff(hit: Bool, +live: List<&2, Bool>, +failed: List<&2, Bool>) -> {(Bool.not(Tl.any(live)), Tl.join.marks(Tl.FailFast{}, hit, live, failed)) == (Bool.not(Tl.any(live)), Sp.ff_marks(live, failed, hit)) : Bool & List<&2, Bool>}:
  match hit:
    case True{}:
      %LB.tlb.ff_hit(live, failed) : {(Bool.not(Tl.any(live)), Tl.abort_others(live, failed)) == (Bool.not(Tl.any(live)), _) : Bool & List<&2, Bool>}
      {==}
    case False{}:
      %LB.tlb.ff_none(live, failed) : {(Bool.not(Tl.any(live)), Tl.keep_all(live)) == (Bool.not(Tl.any(live)), _) : Bool & List<&2, Bool>}
      {==}

def TaskLife.task_life_join_fail_fast(live, failed):
  %LB.tlb.any(live) : {Tl.join(Tl.FailFast{}, live, failed) == (Bool.not(_), Sp.ff_marks(live, failed, Sp.some(failed))) : Bool & List<&2, Bool>}
  %LB.tlb.any(failed) : {Tl.join(Tl.FailFast{}, live, failed) == (Bool.not(Tl.any(live)), Sp.ff_marks(live, failed, _)) : Bool & List<&2, Bool>}
  tlj.ff(Tl.any(failed), live, failed)
