# eukhe: the proof of LAW plan_fits_only_unforced

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# a plan that fits found no needed tool
def po.of_none(m: Maybe<&2, Nat>, +L: List<&2, If.Tool>, +ls: List<&2, Nat>, f: {If.plan.of(m, L) == If.Fits{ls} : If.Plan}) -> {m == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{i}:
      LLogicLogic.pq.absurd({Some{i} == None{} : Maybe<&2, Nat>}, Equal.cong(If.Plan, Bool, LA.w2.over, If.Over{i}, If.Fits{ls}, f))

# the scan for a needed tool found none: no id of ls is needed
def po.calm_go(ls: List<&2, If.Tool>, +need: List<&2, Nat>, hit: Bool, eh: {If.needs.at(ls, need) == hit : Bool}, z: {If.needs.go(ls, need, hit) == None{} : Maybe<&2, Nat>}) -> {Infer.plan.none_needed(Infer.strict.ids(ls), need) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case +t <> +rest:
      match hit:
        case True{}:
          LA.w2.mt({Infer.plan.none_needed(Infer.strict.ids(t <> rest), need) == True{} : Bool}, If.Tool.id(t), z)
        case False{}:
          %Equal.sym(Bool, If.elem(need, If.Tool.id(t)), False{}, eh) : {Bool.and(Bool.not(_), Infer.plan.none_needed(Infer.strict.ids(rest), need)) == True{} : Bool}
          po.calm_go(rest, need, If.needs.at(rest, need), {==}, z)

def Infer.plan_fits_only_unforced(cap, ts, need, ls, f):
  +L = Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict.of(cap, ts))
  +M = If.needs.go(L, need, If.needs.at(L, need))
  po.calm_go(L, need, If.needs.at(L, need), {==}, po.of_none(M, L, ls, f))
