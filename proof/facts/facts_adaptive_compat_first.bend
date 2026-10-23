# eukhe: the proof of LAW facts_adaptive_compat_first

import Base
import ../../bend/infer.bend as If
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws

def pf.facts_adaptive_compat_first(b: Bool, a: If.Ans) -> {Fx.adaptive(Some{b}, a) == b : Bool}:
  {==}

def Laws.facts_adaptive_compat_first(b, a):
  pf.facts_adaptive_compat_first(b, a)
