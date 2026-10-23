# eukhe: the proof of LAW fallback_quiet_when_unset

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback.bend as AuxFallback

# LAW fallback_quiet_when_unset: an unset selector keeps the session model
def ppr.fallback_quiet_when_unset(p: Nat, ok: Bool, look: Af.Look, need: Nat) -> {Af.decide(Af.Pass{p, Af.Unset{}, ok, look, need}) == Af.Session{} : Af.Route}:
  {==}

def AuxFallback.fallback_quiet_when_unset(p, ok, look, need):
  ppr.fallback_quiet_when_unset(p, ok, look, need)
