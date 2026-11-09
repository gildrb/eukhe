# eukhe: the proof of LAW plan_fits_unless_forced

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# a needed id is not among the unneeded ones
def pu.clash(-A: Type, a: Bool, -b: Bool, ea: {a == True{} : Bool}, c: {Bool.and(Bool.not(a), b) == True{} : Bool}) -> A:
  match a:
    case True{}:
      LLogicLogic.absurd(A, c)
    case False{}:
      LLogicLogic.absurd(A, ea)

# the rest of the ids is unneeded too
def pu.rest(a: Bool, -b: Bool, ea: {a == False{} : Bool}, c: {Bool.and(Bool.not(a), b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      c
    case True{}:
      LLogicLogic.pq.absurd({b == True{} : Bool}, ea)

# no tool of ls requires a strict schema: the scan for one finds none
def pu.none_go(ls: List<&2, If.ToolPrio>, +need: List<&2, Nat>, hit: Bool, eh: {If.needs.at(ls, need) == hit : Bool}, calm: {Infer.plan.none_needed(Infer.strict.ids(ls), need) == True{} : Bool}) -> {If.needs.go(ls, need, hit) == None{} : Maybe<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case +t <> +rest:
      match hit:
        case True{}:
          pu.clash({If.needs.go(t <> rest, need, True{}) == None{} : Maybe<&2, Nat>}, If.elem(need, If.ToolPrio.id(t)), Infer.plan.none_needed(Infer.strict.ids(rest), need), eh, calm)
        case False{}:
          pu.none_go(rest, need, If.needs.at(rest, need), {==}, pu.rest(If.elem(need, If.ToolPrio.id(t)), Infer.plan.none_needed(Infer.strict.ids(rest), need), eh, calm))

def Infer.plan_fits_unless_forced(cap, ts, need, calm):
  +L = Pair.snd(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(cap, ts))
  %Equal.sym(Maybe<&2, Nat>, If.needs.go(L, need, If.needs.at(L, need)), None{}, pu.none_go(L, need, If.needs.at(L, need), {==}, calm)) : {If.plan.of(_, L) == If.Fits{Infer.strict.ids(L)} : If.Plan}
  %Equal.sym(List<&2, Nat>, If.ids(L), Infer.strict.ids(L), LA.w2.ids(L)) : {If.Fits{_} == If.Fits{Infer.strict.ids(L)} : If.Plan}
  {==}
