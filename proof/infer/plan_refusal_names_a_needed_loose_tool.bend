# eukhe: the proof of LAW plan_refusal_names_a_needed_loose_tool

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ./base.bend as LA

def w2.named(p: If.Plan) -> Nat:
  match p:
    case If.Fits{ls}:
      0n
    case If.Over{i}:
      i

def w2.of_over(m: Maybe<&2, Nat>, +L: List<&2, If.Tool>, +i: Nat, o: {If.plan.of(m, L) == If.Over{i} : If.Plan}) -> {m == Some{i} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      LBoolMisc.pq.absurdF({None{} == Some{i} : Maybe<&2, Nat>}, Equal.cong(If.Plan, Bool, LA.w2.over, If.Fits{If.ids(L)}, If.Over{i}, o))
    case Some{j}:
      %Equal.cong(If.Plan, Nat, w2.named, If.Over{j}, If.Over{i}, o) : {Some{j} == Some{_} : Maybe<&2, Nat>}
      {==}

def w2.or_t(a: Bool) -> {Bool.and(True{}, Bool.or(a, True{})) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def w2.some_go(+ls: List<&2, If.Tool>, +need: List<&2, Nat>, hit: Bool, eh: {If.needs.at(ls, need) == hit : Bool}, +i: Nat, +s: {If.needs.go(ls, need, hit) == Some{i} : Maybe<&2, Nat>}) -> {Bool.and(If.elem(need, i), If.elem(If.ids(ls), i)) == True{} : Bool}:
  match ls:
    case Nil{}:
      LA.w2.mt({Bool.and(If.elem(need, i), False{}) == True{} : Bool}, i, Equal.sym(Maybe<&2, Nat>, None{}, Some{i}, s))
    case t <> rest:
      match hit:
        case True{}:
          +e = Equal.cong(Maybe<&2, Nat>, Nat, m => Maybe.default(&2, Nat, m, 0n), Some{If.Tool.id(t)}, Some{i}, s)
          +na = LA.w2.elem_at(need, i, If.Tool.id(t), Equal.sym(Nat, If.Tool.id(t), i, e), eh)
          %Equal.sym(Nat, If.Tool.id(t), i, e) : {Bool.and(If.elem(need, i), Bool.or(Nat.is_eq(_, i), If.elem(If.ids(rest), i))) == True{} : Bool}
          %LA.pq.eq_refl(i) : {Bool.and(If.elem(need, i), Bool.or(_, If.elem(If.ids(rest), i))) == True{} : Bool}
          %Equal.sym(Bool, If.elem(need, i), True{}, na) : {Bool.and(_, True{}) == True{} : Bool}
          {==}
        case False{}:
          +a = If.Tool.id(t)
          +h = w2.some_go(rest, need, If.needs.at(rest, need), {==}, i, s)
          +hn = LBoolAnd.pq.and_l(If.elem(need, i), If.elem(If.ids(rest), i), h)
          +hr = LBoolAnd.pq.and_r(If.elem(need, i), If.elem(If.ids(rest), i), h)
          %Equal.sym(Bool, If.elem(need, i), True{}, hn) : {Bool.and(_, Bool.or(Nat.is_eq(a, i), If.elem(If.ids(rest), i))) == True{} : Bool}
          %Equal.sym(Bool, If.elem(If.ids(rest), i), True{}, hr) : {Bool.and(True{}, Bool.or(Nat.is_eq(a, i), _)) == True{} : Bool}
          w2.or_t(Nat.is_eq(a, i))

def Infer.plan_refusal_names_a_needed_loose_tool(cap, ts, need, i, o):
  +L = Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict.of(cap, ts))
  +M = If.needs.go(L, need, If.needs.at(L, need))
  %LA.w2.ids(L) : {Bool.and(If.elem(need, i), If.elem(_, i)) == True{} : Bool}
  w2.some_go(L, need, If.needs.at(L, need), {==}, i, w2.of_over(M, L, i, o))
