# eukhe: the proof of LAW facts_adaptive_rulebook_second

import Base
import ../../bend/facts.bend as Fx
import ../../bend/infer.bend as If
import ../../laws/facts.bend as Facts

def pf.facts_adaptive_rulebook_second(a: If.Ans) -> {Fx.adaptive(None{}, a) == Fx.flag(a, False{}) : Bool}:
  {==}

def Facts.facts_adaptive_rulebook_second(a):
  pf.facts_adaptive_rulebook_second(a)
