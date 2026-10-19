# proof_progress_report: lemmas for the laws that a harness failure is
# reported (laws/progress.bend): the auxiliary-model fallback of
# bend/aux_fallback.bend and the skill and template loading of
# bend/skill_load.bend.
#
# Fallbacks. The events of a session come from one pass at a time
# (`Af.go`), so each law is an induction over the passes with any set of
# shown keys. A substitution event of key k comes with a notice of k
# unless the session showed k before; a key joins the shown set only with
# its notice. So every substituted key is shown or noticed, and from an
# empty set, noticed. The other way is simpler: a notice of k comes only
# right after the substitution event of k.
#
# Loading. Each candidate file adds its path to the loaded list when it is
# good, and a diagnostic with its path when it is not. So each candidate's
# path is on one of the two lists. A loaded path and a reported path are
# each the path of some candidate; when no two candidates share a path, no
# path is on both.
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

import Base
import ./aux_fallback.bend as Af
import ./skill_load.bend as Sk

# Logic
# -----

def ppr.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ppr.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : ppr.BD(_, Unit, A)
  Unit{}

def ppr.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ppr.BD(_, A, Unit)
  Unit{}

def ppr.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ppr.absurdF({False{} == True{} : Bool}, h)

def ppr.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ppr.absurdF({b == True{} : Bool}, h)

# a true right side makes the or true
def ppr.or_r(a: Bool, +b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ppr.or_l(a: Bool, b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ppr.absurdF({b == True{} : Bool}, h)

def ppr.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      ppr.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def ppr.nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ppr.nat_eq_refl(p)

def ppr.nat_eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ppr.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      ppr.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, ppr.nat_eq_true(p, q, h))

# Fallbacks
# ---------

def ppr.key_eq_true(a: Af.Key, b: Af.Key, +h: {Af.Key.eq(a, b) == True{} : Bool}) -> {a == b : Af.Key}:
  match a b:
    case Af.K{+ap, +as1, +ar} Af.K{+bp, +bs1, +br}:
      +i = Bool.and(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br))
      +ep = ppr.nat_eq_true(ap, bp, ppr.and_l(Nat.is_eq(ap, bp), i, h))
      +hs = ppr.and_r(Nat.is_eq(ap, bp), i, h)
      +es = ppr.nat_eq_true(as1, bs1, ppr.and_l(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br), hs))
      +er = ppr.nat_eq_true(ar, br, ppr.and_r(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br), hs))
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
      ppr.or_r(Af.listed(sh, k), Bool.or(True{}, Af.listed(Af.notes(t), k)), {==})
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
      h => ppr.absurdF({Bool.or(Af.listed(sh, k), False{}) == True{} : Bool}, h)
    case +x <> +rest:
      +sh2 = Af.after(Af.decide(x), sh)
      ih = ppr.rep_go(rest, sh2, k)
      h => ppr.rep_put(Af.decide(x), sh, k, Af.go(rest, sh2), ih, h)

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
      ppr.or_r(Af.Key.eq(kk, k), Af.listed(Af.subs(t), k), ih(h))
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

# LAW fallback_is_reported: every key the session model was put in place
# of is noticed in the session
def ppr.fallback_is_reported(ps: List<&2, Af.Pass>, +k: Af.Key, h: {Af.listed(Af.subs(Af.run(ps)), k) == True{} : Bool}) -> {Af.listed(Af.notes(Af.run(ps)), k) == True{} : Bool}:
  ppr.rep_go(ps, Nil{}, k)(h)

# LAW fallback_quiet_when_routed: a session notices only keys the session
# model was put in place of
def ppr.fallback_quiet_when_routed(ps: List<&2, Af.Pass>, +k: Af.Key, h: {Af.listed(Af.notes(Af.run(ps)), k) == True{} : Bool}) -> {Af.listed(Af.subs(Af.run(ps)), k) == True{} : Bool}:
  ppr.quiet_go(ps, Nil{}, k)(h)

# LAW fallback_quiet_when_unset: an unset selector keeps the session model
def ppr.fallback_quiet_when_unset(p: Nat, ok: Bool, look: Af.Look, need: Nat) -> {Af.decide(Af.Pass{p, Af.Unset{}, ok, look, need}) == Af.Session{} : Af.Route}:
  {==}

# LAW fallback_quiet_when_same: a selector that names the session model
# keeps the session model
def ppr.fallback_quiet_when_same(p: Nat, ok: Bool, look: Af.Look, need: Nat) -> {Af.decide(Af.Pass{p, Af.Same{}, ok, look, need}) == Af.Session{} : Af.Route}:
  {==}

# Loading
# -------

# a head of a true or keeps it true: or(a, or(A, B)) from or(A, B), in the
# loaded place and in the reported place
def ppr.or_in_l(a: Bool, +x: Bool, +y: Bool, h: {Bool.or(x, y) == True{} : Bool}) -> {Bool.or(Bool.or(a, x), y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ppr.or_in_r(a: Bool, x: Bool, +y: Bool, h: {Bool.or(x, y) == True{} : Bool}) -> {Bool.or(x, Bool.or(a, y)) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      ppr.or_r(a, y, h)

# the candidate x is loaded or reported
def ppr.skill_head(+x: Sk.Cand, +rest: List<&2, Sk.Cand>) -> {Bool.or(Sk.listed(Sk.loaded(x <> rest), Sk.Cand.path(x)), Sk.listed(Sk.named(Sk.diags(x <> rest)), Sk.Cand.path(x))) == True{} : Bool}:
  match x:
    case Sk.Cand{+p, o}:
      match o:
        case Sk.Good{}:
          +a = Sk.listed(Sk.loaded(rest), p)
          ppr.or_l(Bool.or(Nat.is_eq(p, p), a), Sk.listed(Sk.named(Sk.diags(rest)), p), ppr.or_l(Nat.is_eq(p, p), a, ppr.nat_eq_refl(p)))
        case Sk.Unreadable{}:
          +b = Sk.listed(Sk.named(Sk.diags(rest)), p)
          ppr.or_r(Sk.listed(Sk.loaded(rest), p), Bool.or(Nat.is_eq(p, p), b), ppr.or_l(Nat.is_eq(p, p), b, ppr.nat_eq_refl(p)))
        case Sk.Malformed{}:
          +b = Sk.listed(Sk.named(Sk.diags(rest)), p)
          ppr.or_r(Sk.listed(Sk.loaded(rest), p), Bool.or(Nat.is_eq(p, p), b), ppr.or_l(Nat.is_eq(p, p), b, ppr.nat_eq_refl(p)))
        case Sk.Incomplete{}:
          +b = Sk.listed(Sk.named(Sk.diags(rest)), p)
          ppr.or_r(Sk.listed(Sk.loaded(rest), p), Bool.or(Nat.is_eq(p, p), b), ppr.or_l(Nat.is_eq(p, p), b, ppr.nat_eq_refl(p)))

# a path loaded or reported in rest stays so with x before rest
def ppr.skill_cons(+x: Sk.Cand, +rest: List<&2, Sk.Cand>, +n: Nat, h: {Bool.or(Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n)) == True{} : Bool}) -> {Bool.or(Sk.listed(Sk.loaded(x <> rest), n), Sk.listed(Sk.named(Sk.diags(x <> rest)), n)) == True{} : Bool}:
  match x:
    case Sk.Cand{+p, o}:
      match o:
        case Sk.Good{}:
          ppr.or_in_l(Nat.is_eq(p, n), Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n), h)
        case Sk.Unreadable{}:
          ppr.or_in_r(Nat.is_eq(p, n), Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n), h)
        case Sk.Malformed{}:
          ppr.or_in_r(Nat.is_eq(p, n), Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n), h)
        case Sk.Incomplete{}:
          ppr.or_in_r(Nat.is_eq(p, n), Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n), h)

# LAW skill_failure_reported: the path of every candidate file is on the
# loaded list or named by a diagnostic
def ppr.skill_failure_reported(cs: List<&2, Sk.Cand>, +c: Sk.Cand, i: Sk.In(c, cs)) -> {Bool.or(Sk.listed(Sk.loaded(cs), Sk.Cand.path(c)), Sk.listed(Sk.named(Sk.diags(cs)), Sk.Cand.path(c))) == True{} : Bool}:
  match cs:
    case Nil{}:
      match i:
    case +x <> +rest:
      match i:
        case Inl{eq}:
          %Equal.sym(Sk.Cand, c, x, eq) : {Bool.or(Sk.listed(Sk.loaded(x <> rest), Sk.Cand.path(_)), Sk.listed(Sk.named(Sk.diags(x <> rest)), Sk.Cand.path(_))) == True{} : Bool}
          ppr.skill_head(x, rest)
        case Inr{it}:
          ppr.skill_cons(x, rest, Sk.Cand.path(c), ppr.skill_failure_reported(rest, c, it))

# a true or with a false-making implication
def ppr.or_mono(a: Bool, +x: Bool, +y: Bool, f: {x == True{} : Bool} -> {y == True{} : Bool}, h: {Bool.or(a, x) == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

# a loaded path is the path of a candidate
def ppr.loaded_sub(cs: List<&2, Sk.Cand>, +q: Nat) -> {Sk.listed(Sk.loaded(cs), q) == True{} : Bool} -> {Sk.listed(Sk.paths(cs), q) == True{} : Bool}:
  match cs:
    case Nil{}:
      h => h
    case x <> +rest:
      match x:
        case Sk.Cand{+p, o}:
          match o:
            case Sk.Good{}:
              h => ppr.or_mono(Nat.is_eq(p, q), Sk.listed(Sk.loaded(rest), q), Sk.listed(Sk.paths(rest), q), ppr.loaded_sub(rest, q), h)
            case Sk.Unreadable{}:
              h => ppr.or_r(Nat.is_eq(p, q), Sk.listed(Sk.paths(rest), q), ppr.loaded_sub(rest, q)(h))
            case Sk.Malformed{}:
              h => ppr.or_r(Nat.is_eq(p, q), Sk.listed(Sk.paths(rest), q), ppr.loaded_sub(rest, q)(h))
            case Sk.Incomplete{}:
              h => ppr.or_r(Nat.is_eq(p, q), Sk.listed(Sk.paths(rest), q), ppr.loaded_sub(rest, q)(h))

# a reported path is the path of a candidate
def ppr.named_sub(cs: List<&2, Sk.Cand>, +q: Nat) -> {Sk.listed(Sk.named(Sk.diags(cs)), q) == True{} : Bool} -> {Sk.listed(Sk.paths(cs), q) == True{} : Bool}:
  match cs:
    case Nil{}:
      h => h
    case x <> +rest:
      match x:
        case Sk.Cand{+p, o}:
          match o:
            case Sk.Good{}:
              h => ppr.or_r(Nat.is_eq(p, q), Sk.listed(Sk.paths(rest), q), ppr.named_sub(rest, q)(h))
            case Sk.Unreadable{}:
              h => ppr.or_mono(Nat.is_eq(p, q), Sk.listed(Sk.named(Sk.diags(rest)), q), Sk.listed(Sk.paths(rest), q), ppr.named_sub(rest, q), h)
            case Sk.Malformed{}:
              h => ppr.or_mono(Nat.is_eq(p, q), Sk.listed(Sk.named(Sk.diags(rest)), q), Sk.listed(Sk.paths(rest), q), ppr.named_sub(rest, q), h)
            case Sk.Incomplete{}:
              h => ppr.or_mono(Nat.is_eq(p, q), Sk.listed(Sk.named(Sk.diags(rest)), q), Sk.listed(Sk.paths(rest), q), ppr.named_sub(rest, q), h)

# a list of paths of rest does not name q when the paths of rest do not
def ppr.not_in(b: Bool, +ns: List<&2, Nat>, +rest: List<&2, Sk.Cand>, +q: Nat, eb: {Sk.listed(ns, q) == b : Bool}, sub: {Sk.listed(ns, q) == True{} : Bool} -> {Sk.listed(Sk.paths(rest), q) == True{} : Bool}, out: {Sk.listed(Sk.paths(rest), q) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      ppr.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, Sk.listed(Sk.paths(rest), q), False{}, Equal.sym(Bool, Sk.listed(Sk.paths(rest), q), True{}, sub(eb)), out))
    case False{}:
      {==}

# a good candidate of path p, c saying whether p is n
def ppr.good_at(c: Bool, +p: Nat, +n: Nat, +rest: List<&2, Sk.Cand>, +ec: {Nat.is_eq(p, n) == c : Bool}, +dp: {Sk.listed(Sk.paths(rest), p) == False{} : Bool}, ih: {Bool.and(Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n)) == False{} : Bool}) -> {Bool.and(Bool.or(c, Sk.listed(Sk.loaded(rest), n)), Sk.listed(Sk.named(Sk.diags(rest)), n)) == False{} : Bool}:
  match c:
    case True{}:
      %ppr.nat_eq_true(p, n, ec) : {Sk.listed(Sk.named(Sk.diags(rest)), _) == False{} : Bool}
      ppr.not_in(Sk.listed(Sk.named(Sk.diags(rest)), p), Sk.named(Sk.diags(rest)), rest, p, {==}, ppr.named_sub(rest, p), dp)
    case False{}:
      ih

# a candidate of path p that does not load, c saying whether p is n
def ppr.bad_at(c: Bool, +p: Nat, +n: Nat, +rest: List<&2, Sk.Cand>, +ec: {Nat.is_eq(p, n) == c : Bool}, +dp: {Sk.listed(Sk.paths(rest), p) == False{} : Bool}, ih: {Bool.and(Sk.listed(Sk.loaded(rest), n), Sk.listed(Sk.named(Sk.diags(rest)), n)) == False{} : Bool}) -> {Bool.and(Sk.listed(Sk.loaded(rest), n), Bool.or(c, Sk.listed(Sk.named(Sk.diags(rest)), n))) == False{} : Bool}:
  match c:
    case True{}:
      +eL = ppr.not_in(Sk.listed(Sk.loaded(rest), p), Sk.loaded(rest), rest, p, {==}, ppr.loaded_sub(rest, p), dp)
      %ppr.nat_eq_true(p, n, ec) : {Bool.and(Sk.listed(Sk.loaded(rest), _), True{}) == False{} : Bool}
      %Equal.sym(Bool, Sk.listed(Sk.loaded(rest), p), False{}, eL) : {Bool.and(_, True{}) == False{} : Bool}
      {==}
    case False{}:
      ih

# LAW skill_loaded_not_failed: when no two candidates share a path, no
# path is both loaded and named by a diagnostic
def ppr.skill_loaded_not_failed(cs: List<&2, Sk.Cand>, +n: Nat, +d: {Sk.distinct(cs) == True{} : Bool}) -> {Bool.and(Sk.listed(Sk.loaded(cs), n), Sk.listed(Sk.named(Sk.diags(cs)), n)) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Sk.Cand{+p, o}:
          match o:
            case Sk.Good{}:
              +nd = Bool.not(Sk.listed(Sk.paths(rest), p))
              +dp = ppr.not_t(Sk.listed(Sk.paths(rest), p), ppr.and_l(nd, Sk.distinct(rest), d))
              ppr.good_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, ppr.skill_loaded_not_failed(rest, n, ppr.and_r(nd, Sk.distinct(rest), d)))
            case Sk.Unreadable{}:
              +nd = Bool.not(Sk.listed(Sk.paths(rest), p))
              +dp = ppr.not_t(Sk.listed(Sk.paths(rest), p), ppr.and_l(nd, Sk.distinct(rest), d))
              ppr.bad_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, ppr.skill_loaded_not_failed(rest, n, ppr.and_r(nd, Sk.distinct(rest), d)))
            case Sk.Malformed{}:
              +nd = Bool.not(Sk.listed(Sk.paths(rest), p))
              +dp = ppr.not_t(Sk.listed(Sk.paths(rest), p), ppr.and_l(nd, Sk.distinct(rest), d))
              ppr.bad_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, ppr.skill_loaded_not_failed(rest, n, ppr.and_r(nd, Sk.distinct(rest), d)))
            case Sk.Incomplete{}:
              +nd = Bool.not(Sk.listed(Sk.paths(rest), p))
              +dp = ppr.not_t(Sk.listed(Sk.paths(rest), p), ppr.and_l(nd, Sk.distinct(rest), d))
              ppr.bad_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, ppr.skill_loaded_not_failed(rest, n, ppr.and_r(nd, Sk.distinct(rest), d)))
