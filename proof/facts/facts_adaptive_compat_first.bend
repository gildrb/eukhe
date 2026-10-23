# eukhe: the proof of LAW facts_adaptive_compat_first

import Base
import ../../bend/facts.bend as Fx
import ../../bend/infer.bend as If
import ../../laws/facts.bend as Facts

def pf.facts_adaptive_compat_first(b: Bool, a: If.Ans) -> {Fx.adaptive(Some{b}, a) == b : Bool}:
  {==}

def Facts.facts_adaptive_compat_first(b, a):
  pf.facts_adaptive_compat_first(b, a)
