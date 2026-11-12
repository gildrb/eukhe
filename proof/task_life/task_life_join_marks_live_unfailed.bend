# eukhe: the proof of LAW task_life_join_marks_live_unfailed
#
# PROOF: keep_all sets no mark (tlj.at_keep), so the premise is false
# there; abort_others sets mark i only as live_i and not failed_i (unset
# past the failed list's end), by induction on the live list (tlj.ao_ok).

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def tlj.at_keep(xs: List<&2, Bool>, i: Nat) -> {Sp.at(Tl.keep_all(xs), i) == False{} : Bool}:
  match xs i:
    case Nil{} _:
      {==}
    case x <> t 0n:
      {==}
    case x <> t 1n+p:
      tlj.at_keep(t, p)

def tlj.LU(live: List<&2, Bool>, failed: List<&2, Bool>, i: Nat) -> Type:
  {Sp.at(live, i) == True{} : Bool} & {Sp.at(failed, i) == False{} : Bool}

def tlj.ao_ok(live: List<&2, Bool>, failed: List<&2, Bool>, i: Nat, +h: {Sp.at(Tl.abort_others(live, failed), i) == True{} : Bool}) -> tlj.LU(live, failed, i):
  match live:
    case Nil{}:
      LB.tlb.absurd_ft(tlj.LU(Nil{}, failed, i), h)
    case +l <> t:
      match failed:
        case Nil{}:
          match i:
            case 0n:
              (h, {==})
            case 1n+p:
              tlj.ao_ok(t, Nil{}, p, h)
        case +f <> u:
          match i:
            case 0n:
              (LB.tlb.and_l(l, Bool.not(f), h), LB.tlb.not_true(f, LB.tlb.and_r(l, Bool.not(f), h)))
            case 1n+p:
              tlj.ao_ok(t, u, p, h)

def tlj.marks_ok(p: Tl.Policy, b: Bool, +live: List<&2, Bool>, +failed: List<&2, Bool>, +i: Nat, h: {Sp.at(Tl.join.marks(p, b, live, failed), i) == True{} : Bool}) -> tlj.LU(live, failed, i):
  match p:
    case Tl.FailFast{}:
      match b:
        case True{}:
          tlj.ao_ok(live, failed, i, h)
        case False{}:
          LB.tlb.absurd_ft(tlj.LU(live, failed, i), Equal.trans(Bool, False{}, Sp.at(Tl.keep_all(live), i), True{}, Equal.sym(Bool, Sp.at(Tl.keep_all(live), i), False{}, tlj.at_keep(live, i)), h))
    case Tl.AllSettled{}:
      LB.tlb.absurd_ft(tlj.LU(live, failed, i), Equal.trans(Bool, False{}, Sp.at(Tl.keep_all(live), i), True{}, Equal.sym(Bool, Sp.at(Tl.keep_all(live), i), False{}, tlj.at_keep(live, i)), h))

def TaskLife.task_life_join_marks_live_unfailed(p, live, failed, i, hit):
  tlj.marks_ok(p, Tl.any(failed), live, failed, i, hit)
