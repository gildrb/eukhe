# eukhe: the laws of area aux_fallback, section model: the reported substitution (M5): the decision
# of a pass and the events of a session of bend/aux_fallback.bend

import Base
import ../../bend/aux_fallback.bend as Af

# (M5) A model the harness substitutes is reported
# ------------------------------------------------
# bend/aux_fallback.bend: the routing of a background summary pass
# through the `auxiliaryModel` setting (`decide_auxiliary_route`) and the
# session's notices (`run`): a pass with a set selector that differs from
# the session model and cannot be used runs on the session model, and the
# user sees a notice row, once per purpose, selector and reason.
#
# Requirements (the header of bend/aux_fallback.bend; Rust
# crates/eukhe-core/src/durable/compaction/auxiliary_model.rs
# `decide_auxiliary_route`, `AuxiliaryNotices`; reason numbers: Rust
# `reason_nat`):
# M5.1: a pass's route, checked in order: an unset selector, or one that
#   names the session model, keeps the session model; a selector
#   allowedModels does not admit falls back (reason 0); a lookup that finds
#   nothing usable falls back with its reason; a found model whose known
#   window (not 0) is smaller than the request falls back (reason 5); else
#   the pass runs on the selector's model. A fallback's key is the purpose,
#   the selector and the reason.
# M5.2: the lookups run only when the gate asks for them: a route the gate
#   decided reads nothing they found.
# M5.3: a session runs passes in order; a pass shows one event of its
#   route: a stay on the session model, a run on the selector's model, or
#   the substitution of the session model, with its key.
# M5.4: the first substitution of each key in a session is followed by a
#   notice of that key; a key the session has noticed stays quiet; there is
#   no notice without a substitution.
# A1 (inferred): a pass's events do not depend on the passes after it.
# A2 (scope): Rust runs Af.gate and Af.settle (through the entry
#   bend/ffi_aux_fallback.bend); its notices (AuxiliaryNotices::take) keep
#   their own set of shown keys with the M5.4 rule and do not run Af.put,
#   Af.after, Af.go or Af.run. The laws on those pin the model of the
#   notices, not the code Rust runs.

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

# LAW fallback_quiet_when_unset: an unset selector runs on the session model, whatever
# allowedModels answers, the lookups found and the request's size (M5.1);
# such a pass shows one stay and no notice by fallback_session_history
law fallback_quiet_when_unset:
  for p: Nat
  for ok: Bool
  for look: Af.Look
  for need: Nat
  {Af.decide(Af.Pass{p, Af.Unset{}, ok, look, need}) == Af.Session{} : Af.Route}

# LAW fallback_quiet_when_same: a selector that names the session model runs on it, whatever
# allowedModels answers, the lookups found and the request's size (M5.1);
# such a pass shows one stay and no notice by fallback_session_history
law fallback_quiet_when_same:
  for p: Nat
  for ok: Bool
  for look: Af.Look
  for need: Nat
  {Af.decide(Af.Pass{p, Af.Same{}, ok, look, need}) == Af.Session{} : Af.Route}

# LAW fallback_pass_refused: a set, different selector falls back with the reason 0 when
# allowedModels does not admit it, whatever the lookups found; admitted,
# with lookups that found nothing usable, it falls back with their reason
# (M5.1)
# EXCLUDES: a disallowed model run or looked up, a lookup failure run
#   anyway, a reason replaced, purpose or selector lost from the key
law fallback_pass_refused:
  for p: Nat
  for s: Nat
  for look: Af.Look
  for r: Nat
  for need: Nat
  {(Af.decide(Af.Pass{p, Af.Other{s}, False{}, look, need}), Af.decide(Af.Pass{p, Af.Other{s}, True{}, Af.Miss{r}, need})) == (Af.Fallback{Af.K{p, s, 0n}}, Af.Fallback{Af.K{p, s, r}}) : Af.Route & Af.Route}

# LAW fallback_pass_runs: an admitted selector whose lookups found a model of window w runs
# on it when w is unknown (0) or at least the request (M5.1)
# EXCLUDES: a fitting model refused, an unknown window read as too small
law fallback_pass_runs:
  for p: Nat
  for s: Nat
  for +w: Nat
  for +need: Nat
  for fit: {Bool.or(Nat.is_eq(w, 0n), Nat.is_le(need, w)) == True{} : Bool}
  {Af.decide(Af.Pass{p, Af.Other{s}, True{}, Af.Hit{w}, need}) == Af.Routed{} : Af.Route}

# LAW fallback_pass_too_small: an admitted selector whose lookups found a model of a known
# window smaller than the request falls back with the reason 5 (M5.1)
# EXCLUDES: a request sent to a model too small for it, another reason
law fallback_pass_too_small:
  for p: Nat
  for s: Nat
  for +w: Nat
  for +need: Nat
  for small: {Nat.is_lt(1n+w, need) == True{} : Bool}
  {Af.decide(Af.Pass{p, Af.Other{s}, True{}, Af.Hit{1n+w}, need}) == Af.Fallback{Af.K{p, s, 5n}} : Af.Route}

# Rust's resolver (decide_auxiliary_route) asks the gate (Af.gate, the
# entry's Gate request) first, runs its lookups only when the gate asks
# for them, then settles the route (Af.settle, the Settle request). The
# laws below pin each of the two steps on every input.

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

# The session (a model: A2)
# -------------------------

# LAW fallback_pass_events: the events of a pass come before the events of the passes after
# it: a session shows each pass's own events in order (A1)
# EXCLUDES: a pass whose shown events depend on the passes after it
law fallback_pass_events:
  for r: Af.Route
  for +sh: List<&2, Af.Key>
  for t: List<&2, Af.Ev>
  {Af.put(r, sh, t) == List.append(&2, Af.Ev, Af.put(r, sh, Nil{}), t) : List<&2, Af.Ev>}

# LAW fallback_listed_complete: a key that occurs in a list of keys is listed in it, wherever it
# stands
# EXCLUDES: a membership that misses a key (only the head read, a field
#   compared wrong), which makes fallback_is_reported or
#   fallback_quiet_when_routed false or vacuous
law fallback_listed_complete:
  for a: List<&2, Af.Key>
  for +k: Af.Key
  for b: List<&2, Af.Key>
  {Af.listed(List.append(&2, Af.Key, a, k <> b), k) == True{} : Bool}

# LAW fallback_listed_sound: a key listed in a list of keys occurs in it: the list is some keys,
# then that key, then some keys
# EXCLUDES: a membership that admits a key the list does not hold (a field
#   ignored), which makes fallback_is_reported or
#   fallback_quiet_when_routed vacuous
law fallback_listed_sound:
  for +ks: List<&2, Af.Key>
  for +k: Af.Key
  for h: {Af.listed(ks, k) == True{} : Bool}
  exs a: List<&2, Af.Key>
  exs b: List<&2, Af.Key>
  {ks == List.append(&2, Af.Key, a, k <> b) : List<&2, Af.Key>}

# LAW fallback_event_keys: the substituted keys and the noticed keys of a list of events are
# read event by event, in order: of two lists joined, the keys of the
# first then the keys of the second; a stay or a run has none; a
# substitution of k has the substituted key k and no noticed key; a notice
# of k has the noticed key k and no substituted key
# EXCLUDES: a substitution read as a notice or the reverse, keys lost,
#   added, reordered or deduplicated
law fallback_event_keys:
  for +es: List<&2, Af.Ev>
  for +fs: List<&2, Af.Ev>
  for +k: Af.Key
  {Af.subs(List.append(&2, Af.Ev, es, fs)) == List.append(&2, Af.Key, Af.subs(es), Af.subs(fs)) : List<&2, Af.Key>} & ({Af.notes(List.append(&2, Af.Ev, es, fs)) == List.append(&2, Af.Key, Af.notes(es), Af.notes(fs)) : List<&2, Af.Key>} & {(Af.subs([Af.Stay{}, Af.Went{}]), (Af.subs([Af.Sub{k}]), (Af.subs([Af.Note{k}]), (Af.notes([Af.Stay{}, Af.Went{}, Af.Sub{k}]), Af.notes([Af.Note{k}]))))) == (Nil{}, ([k], (Nil{}, (Nil{}, [k])))) : List<&2, Af.Key> & (List<&2, Af.Key> & (List<&2, Af.Key> & (List<&2, Af.Key> & List<&2, Af.Key>)))})

# the keys the passes ps fell back with, in order, each pass routed by
# Af.decide (a pass that stays or runs adds none)
def afh_fell(r: Af.Route, ks: List<&2, Af.Key>) -> List<&2, Af.Key>:
  match r:
    case Af.Session{}:
      ks
    case Af.Routed{}:
      ks
    case Af.Fallback{k}:
      k <> ks

def afh_fallen(ps: List<&2, Af.Pass>) -> List<&2, Af.Key>:
  match ps:
    case Nil{}:
      Nil{}
    case x <> t:
      afh_fell(Af.decide(x), afh_fallen(t))

# M5.4: the notice of k: none when an earlier pass fell back with k
# (seen), else one
def afh_notice(seen: Bool, k: Af.Key) -> List<&2, Af.Ev>:
  match seen:
    case True{}:
      Nil{}
    case False{}:
      [Af.Note{k}]

# M5.3, M5.4: the events of a pass routed r when the passes before it
# fell back with the keys ks: a stay, a run, or the substitution of key k
# then its notice when no earlier pass fell back with k
def afh_events(r: Af.Route, ks: List<&2, Af.Key>) -> List<&2, Af.Ev>:
  match r:
    case Af.Session{}:
      [Af.Stay{}]
    case Af.Routed{}:
      [Af.Went{}]
    case Af.Fallback{+k}:
      Af.Sub{k} <> afh_notice(Af.listed(ks, k), k)

# LAW fallback_session_history: a session that has run no pass has shown nothing; a session
# that runs one more pass x shows the events it had shown, then x's events
# by its route (Af.decide): a stay, a run, or the substitution of key k,
# then a notice of k when no earlier pass of the session fell back with k
# (M5.3, M5.4; the earlier keys recomputed from the whole history, not
# carried)
# EXCLUDES: a session that forgets (or never keeps) the keys it noticed, so
#   a notice repeats; one that keeps a key it did not substitute, so a
#   notice is lost; a notice before its substitution or after a later
#   pass; passes out of order, dropped or repeated; a session that starts
#   with keys shown or events
law fallback_session_history:
  for +ps: List<&2, Af.Pass>
  for +x: Af.Pass
  {Af.run(Nil{}) == Nil{} : List<&2, Af.Ev>} & {Af.run(List.append(&2, Af.Pass, ps, [x])) == List.append(&2, Af.Ev, Af.run(ps), afh_events(Af.decide(x), afh_fallen(ps))) : List<&2, Af.Ev>}

# the keys ks hold no key twice
def afh_nodup(ks: List<&2, Af.Key>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case k <> +t:
      Bool.and(Bool.not(Af.listed(t, k)), afh_nodup(t))

# LAW fallback_notice_once: a session notices each key (purpose, selector, reason) at most
# once, whatever passes it runs (M5.4)
# EXCLUDES: the same notice row at every compaction of a selector that
#   cannot be used
law fallback_notice_once:
  for +ps: List<&2, Af.Pass>
  {afh_nodup(Af.notes(Af.run(ps))) == True{} : Bool}
