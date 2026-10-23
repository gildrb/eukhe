# eukhe: the proof of LAW fallback_window_fits

import Base
import ../../bend/aux_fallback.bend as Af
import ../../LAWS.bend as Laws

# not (a < b) is b <= a
def paf.nlt_le(a: Nat, b: Nat) -> {Bool.not(Nat.is_lt(a, b)) == Nat.is_le(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      paf.nlt_le(x, y)

def paf.fits(p: Nat, s: Nat, +w: Nat, +need: Nat, fit: {Bool.or(Nat.is_eq(w, 0n), Nat.is_le(need, w)) == True{} : Bool}) -> {Af.settle(Af.Lookup{p, s}, Af.Hit{w}, need) == Af.Routed{} : Af.Route}:
  match w:
    case 0n:
      {==}
    case 1n++x:
      %Equal.sym(Bool, Bool.not(Nat.is_lt(1n+x, need)), Nat.is_le(need, 1n+x), paf.nlt_le(1n+x, need)) : {Af.fits.route(_, p, s) == Af.Routed{} : Af.Route}
      %Equal.sym(Bool, Nat.is_le(need, 1n+x), True{}, fit) : {Af.fits.route(_, p, s) == Af.Routed{} : Af.Route}
      {==}

def Laws.fallback_window_fits(p, s, w, need, fit):
  paf.fits(p, s, w, need, fit)
