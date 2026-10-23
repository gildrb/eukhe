# eukhe: the proof of LAW fallback_quiet_when_same

import Base
import ../../bend/aux_fallback.bend as Af
import ../../LAWS.bend as Laws

# LAW fallback_quiet_when_same: a selector that names the session model
# keeps the session model
def ppr.fallback_quiet_when_same(p: Nat, ok: Bool, look: Af.Look, need: Nat) -> {Af.decide(Af.Pass{p, Af.Same{}, ok, look, need}) == Af.Session{} : Af.Route}:
  {==}

def Laws.fallback_quiet_when_same(p, ok, look, need):
  ppr.fallback_quiet_when_same(p, ok, look, need)
