# eukhe: the laws of area aux_fallback

import Base
import ../bend/aux_fallback.bend as Af
import ../bend/ffi_aux_fallback.bend as FAf
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

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

# ---- aux_fallback_wire ----

# The wire codec of bend/ffi_aux_fallback.bend (grammar: that file's
# header, crates/eukhe-bend/WIRE.md). R1: every request and reply reads
# back; R2: a well-formed request answers the model's answer (Af.gate,
# Af.settle, Af.put and Af.after), encoded; R3: a malformed or overlong
# request answers the error form, never a route. Every input is free.

# what fits the wire: every Nat (and every list length) at most 14 digits
def afw_key_fits(k: Af.Key) -> Bool:
  match k:
    case Af.K{p, s, r}:
      Bool.and(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(r)))

def afw_keys_fit(ks: List<&2, Af.Key>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{k, t}:
      Bool.and(afw_key_fits(k), afw_keys_fit(t))

def afw_route_fits(r: Af.Route) -> Bool:
  match r:
    case Af.Session{}:
      True{}
    case Af.Routed{}:
      True{}
    case Af.Fallback{k}:
      afw_key_fits(k)

def afw_gate_fits(g: Af.Gate) -> Bool:
  match g:
    case Af.Known{r}:
      afw_route_fits(r)
    case Af.Lookup{p, s}:
      Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(s))

def afw_sel_fits(x: Af.Sel) -> Bool:
  match x:
    case Af.Unset{}:
      True{}
    case Af.Same{}:
      True{}
    case Af.Other{s}:
      LawsBase.wire_fits(s)

def afw_look_fits(x: Af.Look) -> Bool:
  match x:
    case Af.Miss{r}:
      LawsBase.wire_fits(r)
    case Af.Hit{w}:
      LawsBase.wire_fits(w)

def afw_ev_fits(e: Af.Ev) -> Bool:
  match e:
    case Af.Stay{}:
      True{}
    case Af.Went{}:
      True{}
    case Af.Sub{k}:
      afw_key_fits(k)
    case Af.Note{k}:
      afw_key_fits(k)

def afw_evs_fit(es: List<&2, Af.Ev>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(afw_ev_fits(e), afw_evs_fit(t))

def afw_req_fits(x: FAf.Req) -> Bool:
  match x:
    case FAf.GateReq{p, sel, ok}:
      Bool.and(LawsBase.wire_fits(p), afw_sel_fits(sel))
    case FAf.SettleReq{g, look, need}:
      Bool.and(afw_gate_fits(g), Bool.and(afw_look_fits(look), LawsBase.wire_fits(need)))
    case FAf.PassReq{r, +sh}:
      Bool.and(afw_route_fits(r), Bool.and(LawsBase.wire_fits(List.length(&2, Af.Key, sh)), afw_keys_fit(sh)))

# the reply to a pass fits: both lists and their lengths
def afw_pass_fits(+es: List<&2, Af.Ev>, +ks: List<&2, Af.Key>) -> Bool:
  Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Af.Ev, es)), afw_evs_fit(es)), Bool.and(LawsBase.wire_fits(List.length(&2, Af.Key, ks)), afw_keys_fit(ks)))

# LAW afw_key_round_trip (R1): a fallback's key that fits reads back
# EXCLUDES: purpose, selector or reason lost, swapped or misread
law afw_key_round_trip:
  for +k: Af.Key
  for rest: String
  for h: {afw_key_fits(k) == True{} : Bool}
  {FAf.get_key(FAf.put_key(k, rest)) == Wr.Got{k, rest} : Wr.Dec<Af.Key>}

# LAW afw_keys_round_trip (R1): a list of keys that fit, of a length that fits, reads back
# EXCLUDES: shown keys lost, added, reordered or misread, a wrong count
law afw_keys_round_trip:
  for +ks: List<&2, Af.Key>
  for rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Af.Key, ks)), afw_keys_fit(ks)) == True{} : Bool}
  {Wr.get_list(~Af.Key, ~FAf.get_key, Wr.put_list(~Af.Key, ~FAf.put_key, ks, rest)) == Wr.Got{ks, rest} : Wr.Dec<List<&2, Af.Key>>}

# LAW afw_route_round_trip (R1): a route that fits reads back (request and reply)
# EXCLUDES: one route read as another, a fallback's key misread
law afw_route_round_trip:
  for +r: Af.Route
  for rest: String
  for h: {afw_route_fits(r) == True{} : Bool}
  {FAf.get_route(FAf.put_route(r, rest)) == Wr.Got{r, rest} : Wr.Dec<Af.Route>}

# LAW afw_gate_round_trip (R1): a gate's answer that fits reads back (request and reply)
# EXCLUDES: a decided route read as a lookup, or the reverse
law afw_gate_round_trip:
  for +g: Af.Gate
  for rest: String
  for h: {afw_gate_fits(g) == True{} : Bool}
  {FAf.get_gate(FAf.put_gate(g, rest)) == Wr.Got{g, rest} : Wr.Dec<Af.Gate>}

# LAW afw_sel_round_trip (R1): a selector that fits reads back
# EXCLUDES: unset read as the session model, a misread selector
law afw_sel_round_trip:
  for +x: Af.Sel
  for rest: String
  for h: {afw_sel_fits(x) == True{} : Bool}
  {FAf.get_sel(FAf.put_sel(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Af.Sel>}

# LAW afw_look_round_trip (R1): a lookup's result that fits reads back
# EXCLUDES: a miss read as a hit, or the reverse; a misread window
law afw_look_round_trip:
  for +x: Af.Look
  for rest: String
  for h: {afw_look_fits(x) == True{} : Bool}
  {FAf.get_look(FAf.put_look(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Af.Look>}

# LAW afw_ev_round_trip (R1): an event that fits reads back
# EXCLUDES: a substitution read as a notice, or the reverse
law afw_ev_round_trip:
  for +e: Af.Ev
  for rest: String
  for h: {afw_ev_fits(e) == True{} : Bool}
  {FAf.get_ev(FAf.put_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Af.Ev>}

# LAW afw_evs_round_trip (R1): a list of events that fit, of a length that fits, reads back
# EXCLUDES: events lost, added, reordered or misread, a wrong count
law afw_evs_round_trip:
  for +es: List<&2, Af.Ev>
  for rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Af.Ev, es)), afw_evs_fit(es)) == True{} : Bool}
  {Wr.get_list(~Af.Ev, ~FAf.get_ev, Wr.put_list(~Af.Ev, ~FAf.put_ev, es, rest)) == Wr.Got{es, rest} : Wr.Dec<List<&2, Af.Ev>>}

# LAW afw_req_round_trip (R1): a request that fits reads back, of every kind
# EXCLUDES: one kind read as another, a field lost, swapped or misread
law afw_req_round_trip:
  for +x: FAf.Req
  for rest: String
  for h: {afw_req_fits(x) == True{} : Bool}
  {FAf.get_req(FAf.put_req(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FAf.Req>}

# LAW afw_pass_round_trip (R1): the reply to a pass, its events then the shown keys, reads back
# EXCLUDES: the two lists swapped, merged or cut
law afw_pass_round_trip:
  for +es: List<&2, Af.Ev>
  for +ks: List<&2, Af.Key>
  for rest: String
  for h: {afw_pass_fits(es, ks) == True{} : Bool}
  {FAf.get_pass(FAf.put_pass((es, ks), rest)) == Wr.Got{(es, ks), rest} : Wr.Dec<+Sigma<List<&2, Af.Ev>, x => List<&2, Af.Key>>>}

# LAW afw_answers_gate (R2): an encoded Gate request answers the model's gate, encoded
# EXCLUDES: an entry that gates other than Af.gate, or drops a field
law afw_answers_gate:
  for +p: Nat
  for +sel: Af.Sel
  for +ok: Bool
  for h: {afw_req_fits(FAf.GateReq{p, sel, ok}) == True{} : Bool}
  {FAf.ffi(FAf.put_req(FAf.GateReq{p, sel, ok}, "")) == FAf.put_gate(Af.gate(p, sel, ok), "") : String}

# LAW afw_answers_settle (R2): an encoded Settle request answers the model's route, encoded
# EXCLUDES: an entry that settles other than Af.settle, or drops a field
law afw_answers_settle:
  for +g: Af.Gate
  for +look: Af.Look
  for +need: Nat
  for h: {afw_req_fits(FAf.SettleReq{g, look, need}) == True{} : Bool}
  {FAf.ffi(FAf.put_req(FAf.SettleReq{g, look, need}, "")) == FAf.put_route(Af.settle(g, look, need), "") : String}

# LAW afw_answers_pass (R2): an encoded Pass request answers the model's events and shown
# keys, encoded
# EXCLUDES: a notice shown twice or lost on the way out, the shown keys
#   of another route
law afw_answers_pass:
  for +r: Af.Route
  for +sh: List<&2, Af.Key>
  for h: {afw_req_fits(FAf.PassReq{r, sh}) == True{} : Bool}
  {FAf.ffi(FAf.put_req(FAf.PassReq{r, sh}, "")) == FAf.put_pass((Af.put(r, sh, Nil{}), Af.after(r, sh)), "") : String}

# LAW afw_malformed (R3): a malformed request answers the error form
# EXCLUDES: a default route for a request it cannot read
law afw_malformed:
  for +s: String
  for h: {FAf.get_req(s) == Wr.Bad{} : Wr.Dec<FAf.Req>}
  {FAf.ffi(s) == Wr.err("aux_fallback: malformed request") : String}

# LAW afw_left_over (R3): a request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law afw_left_over:
  for +x: FAf.Req
  for c: Char
  for rest: String
  for h: {afw_req_fits(x) == True{} : Bool}
  {FAf.ffi(FAf.put_req(x, SCon{c, rest})) == Wr.err("aux_fallback: input left over") : String}

# LAW afw_key_example (R1): anchor and witness: a key is purpose, selector, reason
# EXCLUDES: a vacuous afw_key_round_trip, fields in another order
law afw_key_example:
  {afw_key_fits(Af.K{1n, 2n, 3n}) == True{} : Bool} & {FAf.put_key(Af.K{1n, 2n, 3n}, "") == "1,2,3," : String}

# LAW afw_keys_example (R1): anchor and witness: keys are their count, then each key
# EXCLUDES: a vacuous afw_keys_round_trip
law afw_keys_example:
  {Bool.and(LawsBase.wire_fits(List.length(&2, Af.Key, [Af.K{1n, 2n, 3n}])), afw_keys_fit([Af.K{1n, 2n, 3n}])) == True{} : Bool} & {Wr.put_list(~Af.Key, ~FAf.put_key, [Af.K{1n, 2n, 3n}], "") == "1,1,2,3," : String}

# LAW afw_route_example (R1): anchor and witness: a route is 0 session | 1 routed | 2 key
# EXCLUDES: a vacuous afw_route_round_trip, tags in another order
law afw_route_example:
  {afw_route_fits(Af.Fallback{Af.K{1n, 2n, 3n}}) == True{} : Bool} & {FAf.put_route(Af.Session{}, FAf.put_route(Af.Routed{}, FAf.put_route(Af.Fallback{Af.K{1n, 2n, 3n}}, ""))) == "0,1,2,1,2,3," : String}

# LAW afw_gate_example (R1): anchor and witness: a gate's answer is 0 route | 1 p s
# EXCLUDES: a vacuous afw_gate_round_trip, tags swapped
law afw_gate_example:
  {afw_gate_fits(Af.Lookup{3n, 8n}) == True{} : Bool} & {FAf.put_gate(Af.Known{Af.Routed{}}, FAf.put_gate(Af.Lookup{3n, 8n}, "")) == "0,1,1,3,8," : String}

# LAW afw_sel_example (R1): anchor and witness: a selector is 0 unset | 1 session | 2 s
# EXCLUDES: a vacuous afw_sel_round_trip, tags in another order
law afw_sel_example:
  {afw_sel_fits(Af.Other{8n}) == True{} : Bool} & {FAf.put_sel(Af.Unset{}, FAf.put_sel(Af.Same{}, FAf.put_sel(Af.Other{8n}, ""))) == "0,1,2,8," : String}

# LAW afw_look_example (R1): anchor and witness: a lookup is 0 r (nothing usable) | 1 w (found)
# EXCLUDES: a vacuous afw_look_round_trip, tags swapped
law afw_look_example:
  {afw_look_fits(Af.Hit{10n}) == True{} : Bool} & {FAf.put_look(Af.Miss{4n}, FAf.put_look(Af.Hit{10n}, "")) == "0,4,1,10," : String}

# LAW afw_ev_example (R1): anchor and witness: an event is 0 stay | 1 went | 2 key | 3 key
# EXCLUDES: a vacuous afw_ev_round_trip, tags in another order
law afw_ev_example:
  {afw_ev_fits(Af.Note{Af.K{1n, 2n, 3n}}) == True{} : Bool} & {FAf.put_ev(Af.Stay{}, FAf.put_ev(Af.Went{}, FAf.put_ev(Af.Sub{Af.K{1n, 2n, 3n}}, FAf.put_ev(Af.Note{Af.K{4n, 5n, 6n}}, "")))) == "0,1,2,1,2,3,3,4,5,6," : String}

# LAW afw_evs_example (R1): anchor and witness: events are their count, then each event
# EXCLUDES: a vacuous afw_evs_round_trip
law afw_evs_example:
  {Bool.and(LawsBase.wire_fits(List.length(&2, Af.Ev, [Af.Stay{}, Af.Sub{Af.K{1n, 2n, 3n}}])), afw_evs_fit([Af.Stay{}, Af.Sub{Af.K{1n, 2n, 3n}}])) == True{} : Bool} & {Wr.put_list(~Af.Ev, ~FAf.put_ev, [Af.Stay{}, Af.Sub{Af.K{1n, 2n, 3n}}], "") == "2,0,2,1,2,3," : String}

# LAW afw_gate_req_example (R1): anchor and witness: a Gate request is 0, p, Sel, ok
# EXCLUDES: a vacuous afw_answers_gate, fields in another order
law afw_gate_req_example:
  {afw_req_fits(FAf.GateReq{3n, Af.Other{8n}, True{}}) == True{} : Bool} & {FAf.put_req(FAf.GateReq{3n, Af.Other{8n}, True{}}, "") == "0,3,2,8,T" : String}

# LAW afw_settle_req_example (R1): anchor and witness: a Settle request is 1, GateR, Look, need
# EXCLUDES: a vacuous afw_answers_settle, fields in another order
law afw_settle_req_example:
  {afw_req_fits(FAf.SettleReq{Af.Lookup{3n, 8n}, Af.Hit{10n}, 5n}) == True{} : Bool} & {FAf.put_req(FAf.SettleReq{Af.Lookup{3n, 8n}, Af.Hit{10n}, 5n}, "") == "1,1,3,8,1,10,5," : String}

# LAW afw_pass_req_example (R1): anchor and witness: a Pass request is 2, Route, shown keys
# EXCLUDES: a vacuous afw_answers_pass, fields in another order
law afw_pass_req_example:
  {afw_req_fits(FAf.PassReq{Af.Fallback{Af.K{1n, 2n, 3n}}, [Af.K{1n, 2n, 3n}]}) == True{} : Bool} & {FAf.put_req(FAf.PassReq{Af.Fallback{Af.K{1n, 2n, 3n}}, [Af.K{1n, 2n, 3n}]}, "") == "2,2,1,2,3,1,1,2,3," : String}

# LAW afw_pass_example (R1): anchor and witness: a pass's reply is its events, then its keys
# EXCLUDES: a vacuous afw_pass_round_trip, the lists swapped
law afw_pass_example:
  {afw_pass_fits([Af.Stay{}], [Af.K{1n, 2n, 3n}]) == True{} : Bool} & {FAf.put_pass(([Af.Stay{}], [Af.K{1n, 2n, 3n}]), "") == "1,0,1,1,2,3," : String}

# LAW afw_ffi_example (R2): anchor: a fallback pass with no key shown substitutes and shows
# its notice, end to end
# EXCLUDES: an entry that answers other bytes than the grammar's
law afw_ffi_example:
  {FAf.ffi("2,2,1,2,3,0,") == "2,2,1,2,3,3,1,2,3,1,1,2,3," : String}

# LAW afw_malformed_example (R3): witness: a request of an unknown kind is malformed
# EXCLUDES: a vacuous afw_malformed
law afw_malformed_example:
  {FAf.get_req("3,") == Wr.Bad{} : Wr.Dec<FAf.Req>} & {FAf.ffi("3,") == Wr.err("aux_fallback: malformed request") : String}

# ---- aux_fallback_entry ----

# The entry, whole: the requests and replies of the grammar (the header of
# bend/ffi_aux_fallback.bend), spelled and read with the wire primitives
# of bend/wire.bend and these spec helpers alone, never with the entry's
# own encoders or decoders, and answered by the spec of the decision and
# of a pass above. With afw_ffi_exact every input's answer follows from
# the spec: an answer that is no error is the reply to the request the
# input spells, every error is one of the two error texts.

def afs_spell_key(k: Af.Key, rest: String) -> String:
  match k:
    case Af.K{p, s, r}:
      Wr.put_nat(p, Wr.put_nat(s, Wr.put_nat(r, rest)))

def afs_spell_route(r: Af.Route, rest: String) -> String:
  match r:
    case Af.Session{}:
      Wr.put_nat(0n, rest)
    case Af.Routed{}:
      Wr.put_nat(1n, rest)
    case Af.Fallback{k}:
      Wr.put_nat(2n, afs_spell_key(k, rest))

def afs_spell_gate(g: Af.Gate, rest: String) -> String:
  match g:
    case Af.Known{r}:
      Wr.put_nat(0n, afs_spell_route(r, rest))
    case Af.Lookup{p, s}:
      Wr.put_nat(1n, Wr.put_nat(p, Wr.put_nat(s, rest)))

def afs_spell_ev(e: Af.Ev, rest: String) -> String:
  match e:
    case Af.Stay{}:
      Wr.put_nat(0n, rest)
    case Af.Went{}:
      Wr.put_nat(1n, rest)
    case Af.Sub{k}:
      Wr.put_nat(2n, afs_spell_key(k, rest))
    case Af.Note{k}:
      Wr.put_nat(3n, afs_spell_key(k, rest))

def afs_spell_sel(x: Af.Sel, rest: String) -> String:
  match x:
    case Af.Unset{}:
      Wr.put_nat(0n, rest)
    case Af.Same{}:
      Wr.put_nat(1n, rest)
    case Af.Other{s}:
      Wr.put_nat(2n, Wr.put_nat(s, rest))

def afs_spell_look(x: Af.Look, rest: String) -> String:
  match x:
    case Af.Miss{r}:
      Wr.put_nat(0n, Wr.put_nat(r, rest))
    case Af.Hit{w}:
      Wr.put_nat(1n, Wr.put_nat(w, rest))

# the request Rust writes for x, then rest
def afs_spell_req(x: FAf.Req, rest: String) -> String:
  match x:
    case FAf.GateReq{p, sel, ok}:
      Wr.put_nat(0n, Wr.put_nat(p, afs_spell_sel(sel, Wr.put_bool(ok, rest))))
    case FAf.SettleReq{g, look, need}:
      Wr.put_nat(1n, afs_spell_gate(g, afs_spell_look(look, Wr.put_nat(need, rest))))
    case FAf.PassReq{r, sh}:
      Wr.put_nat(2n, afs_spell_route(r, Wr.put_list(~Af.Key, ~afs_spell_key, sh, rest)))

# the reply to x: the spec's gate, route, or a pass's events then the
# keys shown after it
def afs_reply(x: FAf.Req) -> String:
  match x:
    case FAf.GateReq{p, sel, ok}:
      afs_spell_gate(afs_gate(p, sel, ok), "")
    case FAf.SettleReq{g, look, need}:
      afs_spell_route(afs_settle(g, look, need), "")
    case FAf.PassReq{+r, +sh}:
      Wr.put_list(~Af.Ev, ~afs_spell_ev, afs_events(r, sh), Wr.put_list(~Af.Key, ~afs_spell_key, afs_after(r, sh), ""))

# Reading: the request at the start of a text, field by field

def afs_read_key.r(p: Nat, s: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Af.Key>:
  match d:
    case Wr.Got{r, rest}:
      Wr.Got{Af.K{p, s, r}, rest}
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_key.s(p: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Af.Key>:
  match d:
    case Wr.Got{s, rest}:
      afs_read_key.r(p, s, Wr.get_nat(rest))
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_key.p(d: Wr.Dec<Nat>) -> Wr.Dec<Af.Key>:
  match d:
    case Wr.Got{p, rest}:
      afs_read_key.s(p, Wr.get_nat(rest))
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_key(s: String) -> Wr.Dec<Af.Key>:
  afs_read_key.p(Wr.get_nat(s))

def afs_read_route.key(d: Wr.Dec<Af.Key>) -> Wr.Dec<Af.Route>:
  match d:
    case Wr.Got{k, rest}:
      Wr.Got{Af.Fallback{k}, rest}
    case Wr.Bad{}:
      Wr.Bad{}

# tags: 0 session, 1 routed, 2 a fallback's key
def afs_read_route.tag(n: Nat, s: String) -> Wr.Dec<Af.Route>:
  match n:
    case 0n:
      Wr.Got{Af.Session{}, s}
    case 1n:
      Wr.Got{Af.Routed{}, s}
    case 2n:
      afs_read_route.key(afs_read_key(s))
    case 3n+x:
      Wr.Bad{}

def afs_read_route.go(d: Wr.Dec<Nat>) -> Wr.Dec<Af.Route>:
  match d:
    case Wr.Got{n, s}:
      afs_read_route.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_route(s: String) -> Wr.Dec<Af.Route>:
  afs_read_route.go(Wr.get_nat(s))

def afs_read_gate.known(d: Wr.Dec<Af.Route>) -> Wr.Dec<Af.Gate>:
  match d:
    case Wr.Got{r, s}:
      Wr.Got{Af.Known{r}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_gate.s(p: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Af.Gate>:
  match d:
    case Wr.Got{s, rest}:
      Wr.Got{Af.Lookup{p, s}, rest}
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_gate.p(d: Wr.Dec<Nat>) -> Wr.Dec<Af.Gate>:
  match d:
    case Wr.Got{p, rest}:
      afs_read_gate.s(p, Wr.get_nat(rest))
    case Wr.Bad{}:
      Wr.Bad{}

# tags: 0 a decided route, 1 a lookup (purpose, selector)
def afs_read_gate.tag(n: Nat, s: String) -> Wr.Dec<Af.Gate>:
  match n:
    case 0n:
      afs_read_gate.known(afs_read_route(s))
    case 1n:
      afs_read_gate.p(Wr.get_nat(s))
    case 2n+x:
      Wr.Bad{}

def afs_read_gate.go(d: Wr.Dec<Nat>) -> Wr.Dec<Af.Gate>:
  match d:
    case Wr.Got{n, s}:
      afs_read_gate.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_gate(s: String) -> Wr.Dec<Af.Gate>:
  afs_read_gate.go(Wr.get_nat(s))

def afs_read_sel.other(d: Wr.Dec<Nat>) -> Wr.Dec<Af.Sel>:
  match d:
    case Wr.Got{s, rest}:
      Wr.Got{Af.Other{s}, rest}
    case Wr.Bad{}:
      Wr.Bad{}

# tags: 0 unset, 1 the session model, 2 a selector
def afs_read_sel.tag(n: Nat, s: String) -> Wr.Dec<Af.Sel>:
  match n:
    case 0n:
      Wr.Got{Af.Unset{}, s}
    case 1n:
      Wr.Got{Af.Same{}, s}
    case 2n:
      afs_read_sel.other(Wr.get_nat(s))
    case 3n+x:
      Wr.Bad{}

def afs_read_sel.go(d: Wr.Dec<Nat>) -> Wr.Dec<Af.Sel>:
  match d:
    case Wr.Got{n, s}:
      afs_read_sel.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_miss(d: Wr.Dec<Nat>) -> Wr.Dec<Af.Look>:
  match d:
    case Wr.Got{r, s}:
      Wr.Got{Af.Miss{r}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_hit(d: Wr.Dec<Nat>) -> Wr.Dec<Af.Look>:
  match d:
    case Wr.Got{w, s}:
      Wr.Got{Af.Hit{w}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# tags: 0 nothing usable (the reason), 1 found (the window)
def afs_read_look.tag(n: Nat, s: String) -> Wr.Dec<Af.Look>:
  match n:
    case 0n:
      afs_read_miss(Wr.get_nat(s))
    case 1n:
      afs_read_hit(Wr.get_nat(s))
    case 2n+x:
      Wr.Bad{}

def afs_read_look.go(d: Wr.Dec<Nat>) -> Wr.Dec<Af.Look>:
  match d:
    case Wr.Got{n, s}:
      afs_read_look.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_gq.ok(p: Nat, sel: Af.Sel, d: Wr.Dec<Bool>) -> Wr.Dec<FAf.Req>:
  match d:
    case Wr.Got{ok, s}:
      Wr.Got{FAf.GateReq{p, sel, ok}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_gq.sel(p: Nat, d: Wr.Dec<Af.Sel>) -> Wr.Dec<FAf.Req>:
  match d:
    case Wr.Got{sel, s}:
      afs_read_gq.ok(p, sel, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_gq(d: Wr.Dec<Nat>) -> Wr.Dec<FAf.Req>:
  match d:
    case Wr.Got{p, s}:
      afs_read_gq.sel(p, afs_read_sel.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_sq.need(g: Af.Gate, look: Af.Look, d: Wr.Dec<Nat>) -> Wr.Dec<FAf.Req>:
  match d:
    case Wr.Got{need, s}:
      Wr.Got{FAf.SettleReq{g, look, need}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_sq.look(g: Af.Gate, d: Wr.Dec<Af.Look>) -> Wr.Dec<FAf.Req>:
  match d:
    case Wr.Got{look, s}:
      afs_read_sq.need(g, look, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_sq(d: Wr.Dec<Af.Gate>) -> Wr.Dec<FAf.Req>:
  match d:
    case Wr.Got{g, s}:
      afs_read_sq.look(g, afs_read_look.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_pq.shown(r: Af.Route, d: Wr.Dec<List<&2, Af.Key>>) -> Wr.Dec<FAf.Req>:
  match d:
    case Wr.Got{sh, s}:
      Wr.Got{FAf.PassReq{r, sh}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def afs_read_pq(d: Wr.Dec<Af.Route>) -> Wr.Dec<FAf.Req>:
  match d:
    case Wr.Got{r, s}:
      afs_read_pq.shown(r, Wr.get_list(~Af.Key, ~afs_read_key, s))
    case Wr.Bad{}:
      Wr.Bad{}

# tags: 0 a gate, 1 a settle, 2 a pass
def afs_read_req.tag(n: Nat, s: String) -> Wr.Dec<FAf.Req>:
  match n:
    case 0n:
      afs_read_gq(Wr.get_nat(s))
    case 1n:
      afs_read_sq(afs_read_gate(s))
    case 2n:
      afs_read_pq(afs_read_route(s))
    case 3n+x:
      Wr.Bad{}

def afs_read_req.go(d: Wr.Dec<Nat>) -> Wr.Dec<FAf.Req>:
  match d:
    case Wr.Got{n, s}:
      afs_read_req.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the start of s
def afs_read_req(s: String) -> Wr.Dec<FAf.Req>:
  afs_read_req.go(Wr.get_nat(s))

def afs_entry.end(done: Bool, x: FAf.Req) -> String:
  match done:
    case True{}:
      afs_reply(x)
    case False{}:
      Wr.err("aux_fallback: input left over")

def afs_entry.go(d: Wr.Dec<FAf.Req>) -> String:
  match d:
    case Wr.Got{x, s}:
      afs_entry.end(Wr.end(s), x)
    case Wr.Bad{}:
      Wr.err("aux_fallback: malformed request")

# the entry's answer to s: the reply to the request s is, when nothing is
# left after it; else one of the two error texts
def afs_entry(s: String) -> String:
  afs_entry.go(afs_read_req(s))

# LAW afw_ffi_exact: on every input the entry answers the spec: the reply (spelled by the spec) to the request the input spells, read by the spec's reader with the wire primitives, when nothing is left after it; `E aux_fallback: input left over` when input is left; `E aux_fallback: malformed request` for any other input
# EXCLUDES: an answer for an input that spells no request, a request read
#   otherwise than the grammar spells it, a reply other than the spec's
#   decision or a pass's spec events and keys, an error text that varies
law afw_ffi_exact:
  for +s: String
  {FAf.ffi(s) == afs_entry(s) : String}

# LAW afw_ffi_spelled: every request Rust writes whose numbers fit the wire, spelled by the spec, gets the spec's reply
# EXCLUDES: a request Rust writes refused, or answered for another request
law afw_ffi_spelled:
  for +x: FAf.Req
  for h: {afw_req_fits(x) == True{} : Bool}
  {FAf.ffi(afs_spell_req(x, "")) == afs_reply(x) : String}

# LAW afw_ffi_spec_example: anchor: the spec answers the grammar's bytes: a gate of a set
# selector allowedModels admits looks it up; a found model too small for
# the request falls back with reason 5; a fallback shown before has no
# notice; a 15-digit purpose and input left over are refused
# EXCLUDES: a vacuous afw_ffi_exact (a spec that refuses everything)
law afw_ffi_spec_example:
  {[afs_entry("0,3,2,8,T"), afs_entry("1,1,3,8,1,10,11,"), afs_entry("2,2,1,2,3,1,1,2,3,"), afs_entry("0,123456789012345,0,T"), afs_entry("0,3,0,Tx")] == ["1,3,8,", "2,3,8,5,", "1,2,1,2,3,1,1,2,3,", Wr.err("aux_fallback: malformed request"), Wr.err("aux_fallback: input left over")] : List<&2, String>}
