# eukhe: the proof of LAW facts_google_unordered_refused
#
# PROOF: a level below the one before it makes that pair of the order
# check false, so the rule is not ordered and gbudget refuses it.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def gu.and2(+x: Bool, +y: Bool) -> {Bool.and(x, Bool.and(y, False{})) == False{} : Bool}:
  %Equal.sym(Bool, Bool.and(y, False{}), False{}, LA.fb.and_false_r(y)) : {Bool.and(x, _) == False{} : Bool}
  LA.fb.and_false_r(x)

def gu.unord(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +x: Bool, +ex: {Nat.is_lt(lo, mi) == x : Bool}, +y: Bool, +ey: {Nat.is_lt(me, lo) == y : Bool}, +z: Bool, +ez: {Nat.is_lt(hi, me) == z : Bool}, +h: {Bool.or(x, Bool.or(y, z)) == True{} : Bool}) -> {Bool.and(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi))) == False{} : Bool}:
  match x:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(mi, lo), False{}, LNat.pi.lt_nle(lo, mi, ex)) : {Bool.and(_, Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi))) == False{} : Bool}
      {==}
    case False{}:
      match y:
        case True{}:
          %Equal.sym(Bool, Nat.is_le(lo, me), False{}, LNat.pi.lt_nle(me, lo, ey)) : {Bool.and(Nat.is_le(mi, lo), Bool.and(_, Nat.is_le(me, hi))) == False{} : Bool}
          LA.fb.and_false_r(Nat.is_le(mi, lo))
        case False{}:
          match z:
            case True{}:
              %Equal.sym(Bool, Nat.is_le(me, hi), False{}, LNat.pi.lt_nle(hi, me, ez)) : {Bool.and(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), _)) == False{} : Bool}
              gu.and2(Nat.is_le(mi, lo), Nat.is_le(lo, me))
            case False{}:
              LLogicLogic.pf.absurd_ft({Bool.and(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi))) == False{} : Bool}, h)

def gu.main(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +c: Fx.Customs, +l: Fx.Lv, +falls: {Facts.rule_falls(mi, lo, me, hi) == True{} : Bool}) -> {Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l) == Fx.Unordered{} : Fx.GB}:
  +o = gu.unord(mi, lo, me, hi, Nat.is_lt(lo, mi), {==}, Nat.is_lt(me, lo), {==}, Nat.is_lt(hi, me), {==}, falls)
  %Equal.sym(Bool, Fx.Budgets.ordered(Fx.Budgets{mi, lo, me, hi}), False{}, o) : {Fx.gbudget.rule(_, Fx.Budgets{mi, lo, me, hi}, c, l) == Fx.Unordered{} : Fx.GB}
  {==}

def Facts.facts_google_unordered_refused(mi, lo, me, hi, c, l, falls):
  gu.main(mi, lo, me, hi, c, l, falls)
