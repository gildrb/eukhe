# eukhe: the proof of LAW facts_rulebook_decides

import Base
import ../../bend/infer.bend as If
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws
import ./base.bend as LA

# Decisions from the rulebook
# ---------------------------

def pf.facts_rulebook_decides(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, +q: If.Query, dflt: Bool, ok: {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == True{} : Bool}, hit: {If.applies(q, r) == True{} : Bool}, top: {If.any_at(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), 1n+If.Rule.rank(r)) == False{} : Bool}) -> {Fx.decide(List.append(&2, If.Rule, pre, r <> post), q, If.Rule.dir(r), dflt) == Nat.is_eq(If.Rule.val(r), 1n) : Bool}:
  +L = List.append(&2, If.Rule, pre, r <> post)
  +D = If.Rule.dir(r)
  +V = If.Rule.val(r)
  %Equal.sym(If.Ans, If.lookup(L, q, D), If.Known{V}, LA.pq.quirk_highest_wins(known, pre, r, post, q, ok, hit, top)) : {Fx.flag(_, dflt) == Nat.is_eq(V, 1n) : Bool}
  {==}

# (S6.10) Model and provider facts are data
# ------------------------------------------

def Laws.facts_rulebook_decides(known, pre, r, post, q, dflt, ok, hit, top):
  pf.facts_rulebook_decides(known, pre, r, post, q, dflt, ok, hit, top)
