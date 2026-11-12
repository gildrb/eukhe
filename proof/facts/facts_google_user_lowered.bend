# eukhe: the proof of LAW facts_google_user_lowered
#
# PROOF: a budget above the high is not below the minimal (the minimal is
# at most the high: LA.fg.mh), so the clamp takes its high branch.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def gl.hi(+g: Bool, +x: Nat, +hi: Nat, +eg: {Nat.is_lt(hi, x) == g : Bool}, +h: {Nat.is_lt(hi, x) == True{} : Bool}) -> {Fx.clamp.hi(g, x, hi) == hi : Nat}:
  match g:
    case True{}:
      {==}
    case False{}:
      LA.fb.clash({Fx.clamp.hi(False{}, x, hi) == hi : Nat}, Nat.is_lt(hi, x), eg, h)

def gl.lo(+c: Bool, +x: Nat, +lo: Nat, +hi: Nat, +ec: {Nat.is_lt(x, lo) == c : Bool}, +h: {Nat.is_lt(hi, x) == True{} : Bool}, +lohi: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Fx.clamp.lo(c, x, lo, hi) == hi : Nat}:
  match c:
    case True{}:
      LA.fb.clash({Fx.clamp.lo(True{}, x, lo, hi) == hi : Nat}, Nat.is_le(lo, hi), LNat.pi.lt_nle(hi, lo, LNat.pc.le_lt_trans(hi, x, lo, LNat.pc.lt_to_le(hi, x, h), ec)), lohi)
    case False{}:
      gl.hi(Nat.is_lt(hi, x), x, hi, {==}, h)

def Facts.facts_google_user_lowered(mi, lo, me, hi, c, l, n, ok, u, high):
  Equal.trans(Fx.GB, Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l), Fx.Tokens{Fx.clamp(n, mi, hi)}, Fx.Tokens{hi}, LA.fg.user(mi, lo, me, hi, c, l, n, ok, u), LA.fg.tok(Fx.clamp(n, mi, hi), hi, gl.lo(Nat.is_lt(n, mi), n, mi, hi, {==}, high, LA.fg.mh(mi, lo, me, hi, ok))))
