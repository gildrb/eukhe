# eukhe: the proof of LAW fallback_window_small

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback.bend as AuxFallback

def paf.small(p: Nat, s: Nat, +w: Nat, +need: Nat, small: {Nat.is_lt(1n+w, need) == True{} : Bool}) -> {Af.settle(Af.Lookup{p, s}, Af.Hit{1n+w}, need) == Af.Fallback{Af.K{p, s, 5n}} : Af.Route}:
  %Equal.sym(Bool, Nat.is_lt(1n+w, need), True{}, small) : {Af.fits.route(Bool.not(_), p, s) == Af.Fallback{Af.K{p, s, 5n}} : Af.Route}
  {==}

def AuxFallback.fallback_window_small(p, s, w, need, small):
  paf.small(p, s, w, need, small)
