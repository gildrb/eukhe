# eukhe: the proof of LAW facts_google_user_raised
#
# PROOF: the clamp of a budget below the minimal takes its first branch.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def gr.lo(+c: Bool, +x: Nat, +lo: Nat, +hi: Nat, +ec: {Nat.is_lt(x, lo) == c : Bool}, +h: {Nat.is_lt(x, lo) == True{} : Bool}) -> {Fx.clamp.lo(c, x, lo, hi) == lo : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      LA.fb.clash({Fx.clamp.lo(False{}, x, lo, hi) == lo : Nat}, Nat.is_lt(x, lo), ec, h)

def Facts.facts_google_user_raised(mi, lo, me, hi, c, l, n, ok, u, low):
  Equal.trans(Fx.GB, Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l), Fx.Tokens{Fx.clamp(n, mi, hi)}, Fx.Tokens{mi}, LA.fg.user(mi, lo, me, hi, c, l, n, ok, u), LA.fg.tok(Fx.clamp(n, mi, hi), mi, gr.lo(Nat.is_lt(n, mi), n, mi, hi, {==}, low)))
