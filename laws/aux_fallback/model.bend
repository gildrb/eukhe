# eukhe: the laws of area aux_fallback, section model: the reported substitution (M5), and the decision and a pass's
# events of bend/aux_fallback.bend, whole

import Base
import ../../bend/aux_fallback.bend as Af

# (M5) A model the harness substitutes is reported
# ------------------------------------------------
# bend/aux_fallback.bend: the routing of a background summary pass
# through the `auxiliaryModel` setting (`decide_auxiliary_route`) and the
# session's notices (`run`): a pass with a set selector that differs from
# the session model and cannot be used runs on the session model, and the
# user sees a notice row, once per purpose, selector and reason.

# LAW fallback_is_reported: every substitution of the session model for a set auxiliary
# selector has a notice
law fallback_is_reported:
  for ps: List<&2, Af.Pass>
  for +k: Af.Key
  for h: {Af.listed(Af.subs(Af.run(ps)), k) == True{} : Bool}
  {Af.listed(Af.notes(Af.run(ps)), k) == True{} : Bool}

# LAW fallback_quiet_when_routed: a notice comes only from a substitution
law fallback_quiet_when_routed:
  for ps: List<&2, Af.Pass>
  for +k: Af.Key
  for h: {Af.listed(Af.notes(Af.run(ps)), k) == True{} : Bool}
  {Af.listed(Af.subs(Af.run(ps)), k) == True{} : Bool}

# LAW fallback_quiet_when_unset: an unset selector runs on the session model with no notice
law fallback_quiet_when_unset:
  for p: Nat
  for ok: Bool
  for look: Af.Look
  for need: Nat
  {Af.decide(Af.Pass{p, Af.Unset{}, ok, look, need}) == Af.Session{} : Af.Route}

# LAW fallback_quiet_when_same: a selector that names the session model runs on it with no notice
law fallback_quiet_when_same:
  for p: Nat
  for ok: Bool
  for look: Af.Look
  for need: Nat
  {Af.decide(Af.Pass{p, Af.Same{}, ok, look, need}) == Af.Session{} : Af.Route}

# The Rust resolver asks the gate (Af.gate) first, runs the lookups only
# when the gate asks for them, then settles the route (Af.settle); it
# shows, pass by pass, the events of Af.put and keeps the keys of
# Af.after. The laws below pin that protocol to the session's model.

# LAW fallback_gate_then_settle: a pass's route is its gate settled with its lookups
# EXCLUDES: a resolver whose two steps decide otherwise than the model
law fallback_gate_then_settle:
  for p: Nat
  for sel: Af.Sel
  for ok: Bool
  for look: Af.Look
  for need: Nat
  {Af.decide(Af.Pass{p, sel, ok, look, need}) == Af.settle(Af.gate(p, sel, ok), look, need) : Af.Route}

# LAW fallback_known_needs_no_lookup: a gate that decided reads nothing the lookups found, so they need
# not run
# EXCLUDES: a route that depends on lookups the resolver skipped
law fallback_known_needs_no_lookup:
  for r: Af.Route
  for look: Af.Look
  for need: Nat
  {Af.settle(Af.Known{r}, look, need) == r : Af.Route}

# LAW fallback_gate_other: a set, different selector that allowedModels admits is looked up;
# one it does not admit falls back with the reason 0 (not allowed)
# EXCLUDES: lookups for a disallowed model, a disallowed model run, a
#   wrong reason
law fallback_gate_other:
  for p: Nat
  for s: Nat
  {(Af.gate(p, Af.Other{s}, True{}), Af.gate(p, Af.Other{s}, False{})) == (Af.Lookup{p, s}, Af.Known{Af.Fallback{Af.K{p, s, 0n}}}) : Af.Gate & Af.Gate}

# LAW fallback_gate_session: an unset or same selector keeps the session model without a
# lookup
# EXCLUDES: lookups (credential reads) for a pass that runs on the
#   session model
law fallback_gate_session:
  for p: Nat
  for ok: Bool
  {(Af.gate(p, Af.Unset{}, ok), Af.gate(p, Af.Same{}, ok)) == (Af.Known{Af.Session{}}, Af.Known{Af.Session{}}) : Af.Gate & Af.Gate}

# LAW fallback_miss_keeps_reason: lookups that find nothing usable fall back with their reason
# EXCLUDES: a lookup failure run anyway, its reason replaced
law fallback_miss_keeps_reason:
  for p: Nat
  for s: Nat
  for r: Nat
  for need: Nat
  {Af.settle(Af.Lookup{p, s}, Af.Miss{r}, need) == Af.Fallback{Af.K{p, s, r}} : Af.Route}

# LAW fallback_window_fits: a found model whose window is unknown (0) or at least the request
# runs the pass (a window saturated at the wire's largest Nat is at
# least every request)
# EXCLUDES: a fitting model refused, an unknown window read as too small
law fallback_window_fits:
  for p: Nat
  for s: Nat
  for +w: Nat
  for +need: Nat
  for fit: {Bool.or(Nat.is_eq(w, 0n), Nat.is_le(need, w)) == True{} : Bool}
  {Af.settle(Af.Lookup{p, s}, Af.Hit{w}, need) == Af.Routed{} : Af.Route}

# LAW fallback_window_small: a found model whose known window is smaller than the request falls
# back with the reason 5 (window too small)
# EXCLUDES: a request sent to a model too small for it
law fallback_window_small:
  for p: Nat
  for s: Nat
  for +w: Nat
  for +need: Nat
  for small: {Nat.is_lt(1n+w, need) == True{} : Bool}
  {Af.settle(Af.Lookup{p, s}, Af.Hit{1n+w}, need) == Af.Fallback{Af.K{p, s, 5n}} : Af.Route}

# LAW fallback_pass_events: the events of a pass come before the events of the passes after
# it: a session shows each pass's own events in order
# EXCLUDES: a pass whose shown events depend on the passes after it
law fallback_pass_events:
  for r: Af.Route
  for +sh: List<&2, Af.Key>
  for t: List<&2, Af.Ev>
  {Af.put(r, sh, t) == List.append(&2, Af.Ev, Af.put(r, sh, Nil{}), t) : List<&2, Af.Ev>}

# The decision and a pass's events, whole
# ---------------------------------------
# Written from the requirement (the header of bend/aux_fallback.bend:
# Rust `decide_auxiliary_route` and `AuxiliaryNotices::take`), never
# calling the model: the laws above pin properties of the model; these
# pin its every answer, so the entry's replies follow from them alone.

# what the decision knows before the lookups: an unset selector or the
# session model's keeps the session model; a selector allowedModels does
# not admit falls back with the reason 0; any other is looked up
def afs_gate(p: Nat, sel: Af.Sel, ok: Bool) -> Af.Gate:
  match sel:
    case Af.Unset{}:
      Af.Known{Af.Session{}}
    case Af.Same{}:
      Af.Known{Af.Session{}}
    case Af.Other{s}:
      match ok:
        case True{}:
          Af.Lookup{p, s}
        case False{}:
          Af.Known{Af.Fallback{Af.K{p, s, 0n}}}

# a found model of window w runs a request of size need: an unknown
# window (0), or one at least the request
def afs_fits(+w: Nat, +need: Nat) -> Bool:
  Bool.or(Nat.is_eq(w, 0n), Nat.is_le(need, w))

def afs_hit(ok: Bool, p: Nat, s: Nat) -> Af.Route:
  match ok:
    case True{}:
      Af.Routed{}
    case False{}:
      Af.Fallback{Af.K{p, s, 5n}}

# the route of the lookups of selector s for purpose p: nothing usable
# falls back with its reason; a found model runs the pass when it fits,
# else falls back with the reason 5
def afs_found(p: Nat, s: Nat, look: Af.Look, +need: Nat) -> Af.Route:
  match look:
    case Af.Miss{r}:
      Af.Fallback{Af.K{p, s, r}}
    case Af.Hit{w}:
      afs_hit(afs_fits(w, need), p, s)

# the route: a known one, or the one the lookups give
def afs_settle(g: Af.Gate, look: Af.Look, +need: Nat) -> Af.Route:
  match g:
    case Af.Known{r}:
      r
    case Af.Lookup{p, s}:
      afs_found(p, s, look, need)

# two keys name the same purpose, selector and reason
def afs_same(a: Af.Key, b: Af.Key) -> Bool:
  match a b:
    case Af.K{ap, as1, ar} Af.K{bp, bs1, br}:
      Bool.and(Nat.is_eq(ap, bp), Bool.and(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br)))

# the session has shown k: a key of sh is k
def afs_shown(sh: List<&2, Af.Key>, +k: Af.Key) -> Bool:
  match sh:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(afs_same(x, k), afs_shown(t, k))

def afs_noted(seen: Bool, +k: Af.Key) -> List<&2, Af.Ev>:
  match seen:
    case True{}:
      [Af.Sub{k}]
    case False{}:
      [Af.Sub{k}, Af.Note{k}]

# the events of one pass routed r, the keys sh shown before it: a stay on
# the session model, a run on the selector's model, or the substitution,
# then its notice when the session has not shown its key
def afs_events(r: Af.Route, +sh: List<&2, Af.Key>) -> List<&2, Af.Ev>:
  match r:
    case Af.Session{}:
      [Af.Stay{}]
    case Af.Routed{}:
      [Af.Went{}]
    case Af.Fallback{+k}:
      afs_noted(afs_shown(sh, k), k)

def afs_join(seen: Bool, k: Af.Key, sh: List<&2, Af.Key>) -> List<&2, Af.Key>:
  match seen:
    case True{}:
      sh
    case False{}:
      k <> sh

# the keys shown after a pass routed r: a fallback's key joins, first,
# when the session had not shown it
def afs_after(r: Af.Route, +sh: List<&2, Af.Key>) -> List<&2, Af.Key>:
  match r:
    case Af.Session{}:
      sh
    case Af.Routed{}:
      sh
    case Af.Fallback{+k}:
      afs_join(afs_shown(sh, k), k, sh)

# the keys of the substitution events of es, in order
def afs_subs(es: List<&2, Af.Ev>) -> List<&2, Af.Key>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Af.Stay{}:
          afs_subs(rest)
        case Af.Went{}:
          afs_subs(rest)
        case Af.Sub{k}:
          k <> afs_subs(rest)
        case Af.Note{k}:
          afs_subs(rest)

# the keys of the notice events of es, in order
def afs_notes(es: List<&2, Af.Ev>) -> List<&2, Af.Key>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Af.Stay{}:
          afs_notes(rest)
        case Af.Went{}:
          afs_notes(rest)
        case Af.Sub{k}:
          afs_notes(rest)
        case Af.Note{k}:
          k <> afs_notes(rest)

# LAW fallback_terms_exact: the model's terms the laws above read mean what the spec says: listed is membership by purpose, selector and reason; subs and notes are the keys of the substitution and of the notice events, in order
# EXCLUDES: a membership, substitution or notice reading that makes
#   fallback_is_reported or fallback_quiet_when_routed hold vacuously
law fallback_terms_exact:
  for ks: List<&2, Af.Key>
  for +k: Af.Key
  for es: List<&2, Af.Ev>
  for fs: List<&2, Af.Ev>
  {Af.listed(ks, k) == afs_shown(ks, k) : Bool} & {Af.subs(es) == afs_subs(es) : List<&2, Af.Key>} & {Af.notes(fs) == afs_notes(fs) : List<&2, Af.Key>}

# LAW fallback_decide_exact: the gate and the route of every pass are the spec's: an unset or same selector keeps the session model, a selector allowedModels does not admit falls back with reason 0, any other is looked up; a lookup that finds nothing usable falls back with its reason, a found model runs the pass when its window is unknown (0) or at least the request, else falls back with reason 5
# EXCLUDES: a route or a reason the requirement does not give, for any
#   selector, lookup, window or request size
law fallback_decide_exact:
  for p: Nat
  for sel: Af.Sel
  for ok: Bool
  for g: Af.Gate
  for look: Af.Look
  for +need: Nat
  {Af.gate(p, sel, ok) == afs_gate(p, sel, ok) : Af.Gate} & {Af.settle(g, look, need) == afs_settle(g, look, need) : Af.Route}

# LAW fallback_pass_exact: the events and the shown keys of every pass are the spec's: a stay, a run on the selector's model, or the substitution then its notice when its key was not shown; the key joins the shown keys, first, when it was not shown
# EXCLUDES: an event lost, added or reordered, a notice shown twice for a
#   key or never, a shown key lost or added
law fallback_pass_exact:
  for +r: Af.Route
  for +sh: List<&2, Af.Key>
  {Af.put(r, sh, Nil{}) == afs_events(r, sh) : List<&2, Af.Ev>} & {Af.after(r, sh) == afs_after(r, sh) : List<&2, Af.Key>}

# the route of the pass x: its gate settled with its lookups
def afs_route(x: Af.Pass) -> Af.Route:
  match x:
    case Af.Pass{p, sel, ok, look, need}:
      afs_settle(afs_gate(p, sel, ok), look, need)

# the events of a session that runs the passes ps in order, the keys sh
# shown before them: the first pass's events, then the events of the
# passes after it with the keys shown after it
def afs_go(ps: List<&2, Af.Pass>, +sh: List<&2, Af.Key>) -> List<&2, Af.Ev>:
  match ps:
    case Nil{}:
      Nil{}
    case +x <> rest:
      List.append(&2, Af.Ev, afs_events(afs_route(x), sh), afs_go(rest, afs_after(afs_route(x), sh)))

# LAW fallback_go_exact: the events of every session are the spec's: each pass, in order, shows the spec's events for its route and the keys shown before it, and the keys it shows carry to the passes after it; a session starts with no key shown
# EXCLUDES: a session that never remembers (or forgets) the keys it has
#   shown, so a notice repeats for a key already shown; one that
#   remembers a key it did not show, so a notice is lost; passes run out
#   of order, a pass dropped or repeated, a session that starts with keys
#   shown
law fallback_go_exact:
  for ps: List<&2, Af.Pass>
  for +sh: List<&2, Af.Key>
  for qs: List<&2, Af.Pass>
  {Af.go(ps, sh) == afs_go(ps, sh) : List<&2, Af.Ev>} & {Af.run(qs) == afs_go(qs, Nil{}) : List<&2, Af.Ev>}
