# eukhe: the proof of LAW facts_only_the_rulebook_decides

import Base
import ../../bend/facts.bend as Fx
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer

def pf.facts_only_the_rulebook_decides(+rs: List<&2, If.Rule>, +q1: If.Query, +q2: If.Query, +d: Nat, dflt: Bool, same: {If.lookup(rs, q1, d) == If.lookup(rs, q2, d) : If.Ans}) -> {Fx.decide(rs, q1, d, dflt) == Fx.decide(rs, q2, d, dflt) : Bool}:
  %same : {Fx.flag(If.lookup(rs, q1, d), dflt) == Fx.flag(_, dflt) : Bool}
  {==}

def Infer.facts_only_the_rulebook_decides(rs, q1, q2, d, dflt, same):
  pf.facts_only_the_rulebook_decides(rs, q1, q2, d, dflt, same)
