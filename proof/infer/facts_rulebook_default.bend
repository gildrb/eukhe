# eukhe: the proof of LAW facts_rulebook_default

import Base
import ../../bend/facts.bend as Fx
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ./base.bend as LA

def pf.facts_rulebook_default(+rs: List<&2, If.Rule>, +q: If.Query, +d: Nat, dflt: Bool, none: {If.any_at(rs, q, d, 0n) == False{} : Bool}) -> {Fx.decide(rs, q, d, dflt) == dflt : Bool}:
  %Equal.sym(If.Ans, If.lookup(rs, q, d), If.Unknown{}, LA.pq.quirk_unknown_when_none(rs, q, d, none)) : {Fx.flag(_, dflt) == dflt : Bool}
  {==}

def Infer.facts_rulebook_default(rs, q, d, dflt, none):
  pf.facts_rulebook_default(rs, q, d, dflt, none)
