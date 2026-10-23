# eukhe: the proof of LAW facts_adaptive_rulebook_second

import Base
import ../../bend/infer.bend as If
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws

def pf.facts_adaptive_rulebook_second(a: If.Ans) -> {Fx.adaptive(None{}, a) == Fx.flag(a, False{}) : Bool}:
  {==}

def Laws.facts_adaptive_rulebook_second(a):
  pf.facts_adaptive_rulebook_second(a)
