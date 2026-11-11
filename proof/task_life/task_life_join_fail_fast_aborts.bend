# eukhe: the proof of LAW task_life_join_fail_fast_aborts
#
# PROOF: a set failed flag j makes any true (tlj.at_any), so failFast's
# marks are abort_others'; by induction on the live list, abort_others
# sets mark i for a live task i that did not fail (tlj.ao_hit).

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def tlj.at_any(fs: List<&2, Bool>, j: Nat, e: {Sp.at(fs, j) == True{} : Bool}) -> {Tl.any(fs) == True{} : Bool}:
  match fs:
    case Nil{}:
      LB.tlb.absurd_ft({Tl.any(Nil{}) == True{} : Bool}, e)
    case x <> t:
      match x:
        case True{}:
          {==}
        case False{}:
          match j:
            case 0n:
              LB.tlb.absurd_ft({Tl.any(False{} <> t) == True{} : Bool}, e)
            case 1n+q:
              tlj.at_any(t, q, e)

def tlj.ao_hit(live: List<&2, Bool>, failed: List<&2, Bool>, i: Nat, up: {Sp.at(live, i) == True{} : Bool}, ok: {Sp.at(failed, i) == False{} : Bool}) -> {Sp.at(Tl.abort_others(live, failed), i) == True{} : Bool}:
  match live:
    case Nil{}:
      LB.tlb.absurd_ft({Sp.at(Tl.abort_others(Nil{}, failed), i) == True{} : Bool}, up)
    case +l <> t:
      match failed:
        case Nil{}:
          match i:
            case 0n:
              up
            case 1n+p:
              tlj.ao_hit(t, Nil{}, p, up, ok)
        case +f <> u:
          match i:
            case 0n:
              %Equal.sym(Bool, l, True{}, up) : {Bool.and(_, Bool.not(f)) == True{} : Bool}
              %Equal.sym(Bool, f, False{}, ok) : {Bool.and(True{}, Bool.not(_)) == True{} : Bool}
              {==}
            case 1n+p:
              tlj.ao_hit(t, u, p, up, ok)

def TaskLife.task_life_join_fail_fast_aborts(live, failed, i, j, one, up, ok):
  %Equal.sym(Bool, Tl.any(failed), True{}, tlj.at_any(failed, j, one)) : {Sp.at(Tl.join.marks(Tl.FailFast{}, _, live, failed), i) == True{} : Bool}
  tlj.ao_hit(live, failed, i, up, ok)
