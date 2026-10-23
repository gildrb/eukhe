# eukhe: the proof of LAW fallback_pass_events

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback.bend as AuxFallback

def paf.noted(b: Bool, k: Af.Key, t: List<&2, Af.Ev>) -> {Af.noted(b, k, t) == List.append(&2, Af.Ev, Af.noted(b, k, Nil{}), t) : List<&2, Af.Ev>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def paf.put(r: Af.Route, +sh: List<&2, Af.Key>, t: List<&2, Af.Ev>) -> {Af.put(r, sh, t) == List.append(&2, Af.Ev, Af.put(r, sh, Nil{}), t) : List<&2, Af.Ev>}:
  match r:
    case Af.Session{}:
      {==}
    case Af.Routed{}:
      {==}
    case Af.Fallback{+k}:
      Equal.cong(List<&2, Af.Ev>, List<&2, Af.Ev>, e => Af.Sub{k} <> e, Af.noted(Af.listed(sh, k), k, t), List.append(&2, Af.Ev, Af.noted(Af.listed(sh, k), k, Nil{}), t), paf.noted(Af.listed(sh, k), k, t))

def AuxFallback.fallback_pass_events(r, sh, t):
  paf.put(r, sh, t)
