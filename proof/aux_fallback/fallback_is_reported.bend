# eukhe: the proof of LAW fallback_is_reported

import Base
import ../../bend/aux_fallback.bend as Af
import ../../LAWS.bend as Laws
import ../base.bend as L

# Fallbacks
# ---------

def ppr.key_eq_true(a: Af.Key, b: Af.Key, +h: {Af.Key.eq(a, b) == True{} : Bool}) -> {a == b : Af.Key}:
  match a b:
    case Af.K{+ap, +as1, +ar} Af.K{+bp, +bs1, +br}:
      +i = Bool.and(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br))
      +ep = L.ppr.nat_eq_true(ap, bp, L.ppr.and_l(Nat.is_eq(ap, bp), i, h))
      +hs = L.ppr.and_r(Nat.is_eq(ap, bp), i, h)
      +es = L.ppr.nat_eq_true(as1, bs1, L.ppr.and_l(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br), hs))
      +er = L.ppr.nat_eq_true(ar, br, L.ppr.and_r(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br), hs))
      %ep : {Af.K{ap, as1, ar} == Af.K{_, bs1, br} : Af.Key}
      %es : {Af.K{ap, as1, ar} == Af.K{ap, _, br} : Af.Key}
      %er : {Af.K{ap, as1, ar} == Af.K{ap, as1, _} : Af.Key}
      {==}

# a fallback the session showed before, of a key c says is k: k is shown
def ppr.rep_seen(c: Bool, +sh: List<&2, Af.Key>, +kk: Af.Key, +k: Af.Key, +t: List<&2, Af.Ev>, +ec: {Af.Key.eq(kk, k) == c : Bool}, es: {Af.listed(sh, kk) == True{} : Bool}, ih: {Af.listed(Af.subs(t), k) == True{} : Bool} -> {Bool.or(Af.listed(sh, k), Af.listed(Af.notes(t), k)) == True{} : Bool}, h: {Bool.or(c, Af.listed(Af.subs(t), k)) == True{} : Bool}) -> {Bool.or(Af.listed(sh, k), Af.listed(Af.notes(t), k)) == True{} : Bool}:
  match c:
    case True{}:
      %ppr.key_eq_true(kk, k, ec) : {Bool.or(Af.listed(sh, _), Af.listed(Af.notes(t), _)) == True{} : Bool}
      %Equal.sym(Bool, Af.listed(sh, kk), True{}, es) : {Bool.or(_, Af.listed(Af.notes(t), kk)) == True{} : Bool}
      {==}
    case False{}:
      ih(h)

# a fallback the session had not shown, of a key c says is k: k is
# noticed now, or later
def ppr.rep_new(c: Bool, +sh: List<&2, Af.Key>, +k: Af.Key, +t: List<&2, Af.Ev>, ih: {Af.listed(Af.subs(t), k) == True{} : Bool} -> {Bool.or(Bool.or(c, Af.listed(sh, k)), Af.listed(Af.notes(t), k)) == True{} : Bool}, h: {Bool.or(c, Af.listed(Af.subs(t), k)) == True{} : Bool}) -> {Bool.or(Af.listed(sh, k), Bool.or(c, Af.listed(Af.notes(t), k))) == True{} : Bool}:
  match c:
    case True{}:
      L.ppr.or_r(Af.listed(sh, k), Bool.or(True{}, Af.listed(Af.notes(t), k)), {==})
    case False{}:
      ih(h)

# one fallback of key kk, the session having shown kk or not (seen)
def ppr.rep_fb(seen: Bool, +sh: List<&2, Af.Key>, +kk: Af.Key, +k: Af.Key, +t: List<&2, Af.Ev>, +es: {Af.listed(sh, kk) == seen : Bool}, ih: {Af.listed(Af.subs(t), k) == True{} : Bool} -> {Bool.or(Af.listed(Af.shown(seen, kk, sh), k), Af.listed(Af.notes(t), k)) == True{} : Bool}, h: {Bool.or(Af.Key.eq(kk, k), Af.listed(Af.subs(Af.noted(seen, kk, t)), k)) == True{} : Bool}) -> {Bool.or(Af.listed(sh, k), Af.listed(Af.notes(Af.noted(seen, kk, t)), k)) == True{} : Bool}:
  match seen:
    case True{}:
      ppr.rep_seen(Af.Key.eq(kk, k), sh, kk, k, t, {==}, es, ih, h)
    case False{}:
      ppr.rep_new(Af.Key.eq(kk, k), sh, k, t, ih, h)

# one pass routed r: a substituted key of its events, or of the events t
# after it, is shown or noticed
def ppr.rep_put(r: Af.Route, +sh: List<&2, Af.Key>, +k: Af.Key, +t: List<&2, Af.Ev>, ih: {Af.listed(Af.subs(t), k) == True{} : Bool} -> {Bool.or(Af.listed(Af.after(r, sh), k), Af.listed(Af.notes(t), k)) == True{} : Bool}, h: {Af.listed(Af.subs(Af.put(r, sh, t)), k) == True{} : Bool}) -> {Bool.or(Af.listed(sh, k), Af.listed(Af.notes(Af.put(r, sh, t)), k)) == True{} : Bool}:
  match r:
    case Af.Session{}:
      ih(h)
    case Af.Routed{}:
      ih(h)
    case Af.Fallback{+kk}:
      ppr.rep_fb(Af.listed(sh, kk), sh, kk, k, t, {==}, ih, h)

# every substituted key of a session that has shown sh is in sh or
# noticed
def ppr.rep_go(ps: List<&2, Af.Pass>, +sh: List<&2, Af.Key>, +k: Af.Key) -> {Af.listed(Af.subs(Af.go(ps, sh)), k) == True{} : Bool} -> {Bool.or(Af.listed(sh, k), Af.listed(Af.notes(Af.go(ps, sh)), k)) == True{} : Bool}:
  match ps:
    case Nil{}:
      h => L.ppr.absurdF({Bool.or(Af.listed(sh, k), False{}) == True{} : Bool}, h)
    case +x <> +rest:
      +sh2 = Af.after(Af.decide(x), sh)
      ih = ppr.rep_go(rest, sh2, k)
      h => ppr.rep_put(Af.decide(x), sh, k, Af.go(rest, sh2), ih, h)

# LAW fallback_is_reported: every key the session model was put in place
# of is noticed in the session
def ppr.fallback_is_reported(ps: List<&2, Af.Pass>, +k: Af.Key, h: {Af.listed(Af.subs(Af.run(ps)), k) == True{} : Bool}) -> {Af.listed(Af.notes(Af.run(ps)), k) == True{} : Bool}:
  ppr.rep_go(ps, Nil{}, k)(h)

def Laws.fallback_is_reported(ps, k, h):
  ppr.fallback_is_reported(ps, k, h)
