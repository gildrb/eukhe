# eukhe: the proof of LAW fallback_quiet_when_routed

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback.bend as AuxFallback
import ../base/bool/misc.bend as LBoolMisc

# a notice of c's key comes with its substitution
def ppr.quiet_new(c: Bool, +k: Af.Key, +t: List<&2, Af.Ev>, ih: {Af.listed(Af.notes(t), k) == True{} : Bool} -> {Af.listed(Af.subs(t), k) == True{} : Bool}, h: {Bool.or(c, Af.listed(Af.notes(t), k)) == True{} : Bool}) -> {Bool.or(c, Af.listed(Af.subs(t), k)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      ih(h)

# one fallback of key kk: a notice of k is in its events only with the
# substitution of k
def ppr.quiet_fb(seen: Bool, +kk: Af.Key, +k: Af.Key, +t: List<&2, Af.Ev>, ih: {Af.listed(Af.notes(t), k) == True{} : Bool} -> {Af.listed(Af.subs(t), k) == True{} : Bool}, h: {Af.listed(Af.notes(Af.noted(seen, kk, t)), k) == True{} : Bool}) -> {Bool.or(Af.Key.eq(kk, k), Af.listed(Af.subs(Af.noted(seen, kk, t)), k)) == True{} : Bool}:
  match seen:
    case True{}:
      LBoolMisc.ppr.or_r(Af.Key.eq(kk, k), Af.listed(Af.subs(t), k), ih(h))
    case False{}:
      ppr.quiet_new(Af.Key.eq(kk, k), k, t, ih, h)

def ppr.quiet_put(r: Af.Route, +sh: List<&2, Af.Key>, +k: Af.Key, +t: List<&2, Af.Ev>, ih: {Af.listed(Af.notes(t), k) == True{} : Bool} -> {Af.listed(Af.subs(t), k) == True{} : Bool}, h: {Af.listed(Af.notes(Af.put(r, sh, t)), k) == True{} : Bool}) -> {Af.listed(Af.subs(Af.put(r, sh, t)), k) == True{} : Bool}:
  match r:
    case Af.Session{}:
      ih(h)
    case Af.Routed{}:
      ih(h)
    case Af.Fallback{+kk}:
      ppr.quiet_fb(Af.listed(sh, kk), kk, k, t, ih, h)

# every noticed key of a session is a substituted key
def ppr.quiet_go(ps: List<&2, Af.Pass>, +sh: List<&2, Af.Key>, +k: Af.Key) -> {Af.listed(Af.notes(Af.go(ps, sh)), k) == True{} : Bool} -> {Af.listed(Af.subs(Af.go(ps, sh)), k) == True{} : Bool}:
  match ps:
    case Nil{}:
      h => h
    case +x <> +rest:
      +sh2 = Af.after(Af.decide(x), sh)
      ih = ppr.quiet_go(rest, sh2, k)
      h => ppr.quiet_put(Af.decide(x), sh, k, Af.go(rest, sh2), ih, h)

# LAW fallback_quiet_when_routed: a session notices only keys the session
# model was put in place of
def ppr.fallback_quiet_when_routed(ps: List<&2, Af.Pass>, +k: Af.Key, h: {Af.listed(Af.notes(Af.run(ps)), k) == True{} : Bool}) -> {Af.listed(Af.subs(Af.run(ps)), k) == True{} : Bool}:
  ppr.quiet_go(ps, Nil{}, k)(h)

def AuxFallback.fallback_quiet_when_routed(ps, k, h):
  ppr.fallback_quiet_when_routed(ps, k, h)
