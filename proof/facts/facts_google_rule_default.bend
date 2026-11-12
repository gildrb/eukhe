# eukhe: the proof of LAW facts_google_rule_default
#
# PROOF: with no user's budget the clamp holds the rule's budget of the
# level, which a rule that never falls keeps inside minimal..high.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def gd.at(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +l: Fx.Lv, +p1: {Nat.is_le(mi, lo) == True{} : Bool}, +p2: {Nat.is_le(lo, me) == True{} : Bool}, +p3: {Nat.is_le(me, hi) == True{} : Bool}, +mh: {Nat.is_le(mi, hi) == True{} : Bool}) -> {Fx.clamp(Fx.Budgets.at(Fx.Budgets{mi, lo, me, hi}, l), mi, hi) == Facts.rule_at(mi, lo, me, hi, l) : Nat}:
  match l:
    case Fx.Minimal{}:
      LA.fg.kept(mi, mi, hi, LA.facts.pf.le_refl(mi), mh)
    case Fx.Low{}:
      LA.fg.kept(lo, mi, hi, p1, LA.pf.le_trans(lo, me, hi, p2, p3))
    case Fx.Medium{}:
      LA.fg.kept(me, mi, hi, LA.pf.le_trans(mi, lo, me, p1, p2), p3)
    case Fx.High{}:
      LA.fg.kept(hi, mi, hi, mh, LA.facts.pf.le_refl(hi))

def gd.t(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +c: Fx.Customs, +l: Fx.Lv, +h: {Facts.rule_falls(mi, lo, me, hi) == False{} : Bool}, +u: {Facts.customs_spec(c, l) == None{} : Maybe<&2, Nat>}) -> {Fx.Tokens{Fx.gtokens(Fx.Budgets{mi, lo, me, hi}, c, l)} == Fx.Tokens{Facts.rule_at(mi, lo, me, hi, l)} : Fx.GB}:
  +ua = Equal.trans(Maybe<&2, Nat>, Fx.Customs.at(c, l), Facts.customs_spec(c, l), None{}, LA.fg.at(c, l), u)
  %Equal.sym(Maybe<&2, Nat>, Fx.Customs.at(c, l), None{}, ua) : {Fx.Tokens{Fx.clamp(Maybe.default(&2, Nat, _, Fx.Budgets.at(Fx.Budgets{mi, lo, me, hi}, l)), mi, hi)} == Fx.Tokens{Facts.rule_at(mi, lo, me, hi, l)} : Fx.GB}
  LA.fg.tok(Fx.clamp(Fx.Budgets.at(Fx.Budgets{mi, lo, me, hi}, l), mi, hi), Facts.rule_at(mi, lo, me, hi, l), gd.at(mi, lo, me, hi, l, LA.fg.p1(mi, lo, me, hi, h), LA.fg.p2(mi, lo, me, hi, h), LA.fg.p3(mi, lo, me, hi, h), LA.fg.mh(mi, lo, me, hi, h)))

def Facts.facts_google_rule_default(mi, lo, me, hi, c, l, ok, u):
  Equal.trans(Fx.GB, Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l), Fx.Tokens{Fx.gtokens(Fx.Budgets{mi, lo, me, hi}, c, l)}, Fx.Tokens{Facts.rule_at(mi, lo, me, hi, l)}, LA.fg.tokens(mi, lo, me, hi, c, l, ok), gd.t(mi, lo, me, hi, c, l, ok, u))
