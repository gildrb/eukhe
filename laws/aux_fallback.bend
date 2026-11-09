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

# The entry, spelled by the grammar Rust writes and reads
# (crates/eukhe-core/src/durable/compaction/auxiliary_model.rs `gate` and
# `settle`; the header of bend/ffi_aux_fallback.bend), not by the entry's
# own encoders. The answer spelled is the model's own decision (Af.gate,
# Af.settle, Af.put, Af.after), as in the other entries of the compiled
# core: these laws pin the bytes and that the entry answers the model on
# the request it read; the decision itself is pinned by the M5 laws above
# (fallback_gate_other, fallback_gate_session, fallback_miss_keeps_reason,
# fallback_window_fits, fallback_window_small, fallback_is_reported,
# fallback_quiet_when_*), never by a second copy of it here.

# a key: the purpose, the selector, the reason
def afw_spell_key(k: Af.Key, rest: String) -> String:
  match k:
    case Af.K{p, s, r}:
      Wr.put_nat(p, Wr.put_nat(s, Wr.put_nat(r, rest)))

# the keys ks, each spelled, then rest
def afw_spell_key_items(ks: List<&2, Af.Key>, rest: String) -> String:
  match ks:
    case Nil{}:
      rest
    case Con{k, t}:
      afw_spell_key(k, afw_spell_key_items(t, rest))

# a list of keys: its count, then the keys
def afw_spell_keys(+ks: List<&2, Af.Key>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Af.Key, ks), afw_spell_key_items(ks, rest))

# a route: 0 session | 1 routed | 2, then the key (fallback)
def afw_spell_route(r: Af.Route, rest: String) -> String:
  match r:
    case Af.Session{}:
      Wr.put_nat(0n, rest)
    case Af.Routed{}:
      Wr.put_nat(1n, rest)
    case Af.Fallback{k}:
      Wr.put_nat(2n, afw_spell_key(k, rest))

# a gate's answer: 0, then the route (decided) | 1, p, s (look up)
def afw_spell_gate(g: Af.Gate, rest: String) -> String:
  match g:
    case Af.Known{r}:
      Wr.put_nat(0n, afw_spell_route(r, rest))
    case Af.Lookup{p, s}:
      Wr.put_nat(1n, Wr.put_nat(p, Wr.put_nat(s, rest)))

# a selector: 0 unset | 1 the session model | 2, s
def afw_spell_sel(x: Af.Sel, rest: String) -> String:
  match x:
    case Af.Unset{}:
      Wr.put_nat(0n, rest)
    case Af.Same{}:
      Wr.put_nat(1n, rest)
    case Af.Other{s}:
      Wr.put_nat(2n, Wr.put_nat(s, rest))

# what the lookups found: 0, r (nothing usable) | 1, w (a model, its window)
def afw_spell_look(x: Af.Look, rest: String) -> String:
  match x:
    case Af.Miss{r}:
      Wr.put_nat(0n, Wr.put_nat(r, rest))
    case Af.Hit{w}:
      Wr.put_nat(1n, Wr.put_nat(w, rest))

# a request: 0, p, Sel, ok (Gate) | 1, GateR, Look, need (Settle) |
# 2, Route, the shown keys (Pass); then rest
def afw_spell_req(x: FAf.Req, rest: String) -> String:
  match x:
    case FAf.GateReq{p, sel, ok}:
      Wr.put_nat(0n, Wr.put_nat(p, afw_spell_sel(sel, Wr.put_bool(ok, rest))))
    case FAf.SettleReq{g, look, need}:
      Wr.put_nat(1n, afw_spell_gate(g, afw_spell_look(look, Wr.put_nat(need, rest))))
    case FAf.PassReq{r, sh}:
      Wr.put_nat(2n, afw_spell_route(r, afw_spell_keys(sh, rest)))

# an event: 0 stay | 1 went | 2, then the key (substitution) | 3, then the
# key (notice)
def afw_spell_ev(e: Af.Ev, rest: String) -> String:
  match e:
    case Af.Stay{}:
      Wr.put_nat(0n, rest)
    case Af.Went{}:
      Wr.put_nat(1n, rest)
    case Af.Sub{k}:
      Wr.put_nat(2n, afw_spell_key(k, rest))
    case Af.Note{k}:
      Wr.put_nat(3n, afw_spell_key(k, rest))

# the events es, each spelled, then rest
def afw_spell_ev_items(es: List<&2, Af.Ev>, rest: String) -> String:
  match es:
    case Nil{}:
      rest
    case Con{e, t}:
      afw_spell_ev(e, afw_spell_ev_items(t, rest))

# a list of events: its count, then the events
def afw_spell_evs(+es: List<&2, Af.Ev>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Af.Ev, es), afw_spell_ev_items(es, rest))

# the reply Rust reads to request x: the model's gate (Gate), the model's
# route (Settle), or the model's events of the pass then the keys shown
# after it (Pass), each spelled by the grammar
def afw_spell_answer(x: FAf.Req) -> String:
  match x:
    case FAf.GateReq{p, sel, ok}:
      afw_spell_gate(Af.gate(p, sel, ok), "")
    case FAf.SettleReq{g, look, need}:
      afw_spell_route(Af.settle(g, look, need), "")
    case FAf.PassReq{+r, +sh}:
      afw_spell_evs(Af.put(r, sh, Nil{}), afw_spell_keys(Af.after(r, sh), ""))

# LAW afw_answers_spelled: a request spelled by the grammar, every number within the wire,
# answers the grammar's spelling of the model's decision on that request:
# the gate of its purpose, selector and allowedModels flag, the route of
# its gate settled with its lookups, or the events of its pass then the
# keys shown after it
# EXCLUDES: a tag, field order or reason that drifts from the grammar Rust
#   reads and writes (swapped on both sides of the entry alike), a request
#   field lost, swapped or defaulted on its way to the model (the model
#   called with another selector, flag, gate, lookup, need, route or shown
#   keys), the two lists of a pass's reply swapped or cut
law afw_answers_spelled:
  for +x: FAf.Req
  for fits: {afw_req_fits(x) == True{} : Bool}
  {FAf.ffi(afw_spell_req(x, "")) == afw_spell_answer(x) : String}

# LAW afw_left_over_spelled: a spelled request that fits, followed by any more input, answers
# the error form "aux_fallback: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request, or
#   answered with another error text
law afw_left_over_spelled:
  for +x: FAf.Req
  for fits: {afw_req_fits(x) == True{} : Bool}
  for +c: Char
  for +t: String
  {FAf.ffi(afw_spell_req(x, SCon{c, t})) == Wr.err("aux_fallback: input left over") : String}

# LAW afw_reads_only_requests: an answer that is not the error form answers a request: the
# input is exactly the spelling of a request whose numbers fit the wire,
# and the answer is the spelled answer of the model's decision on it
# EXCLUDES: a decoder that accepts an unknown tag (request, selector, gate,
#   lookup, route), a missing or extra field, or input left over, and
#   answers it anyway (a default instead of the error form)
law afw_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FAf.ffi(s)) == False{} : Bool}
  exs x: FAf.Req
  {(s, (afw_req_fits(x), FAf.ffi(s))) == (afw_spell_req(x, ""), (True{}, afw_spell_answer(x))) : String & (Bool & String)}

# LAW afw_malformed_unless_request: every answer but the error form "aux_fallback: malformed
# request" comes from an input that begins with a spelled request that fits
# (with afw_answers_spelled and afw_left_over_spelled: every input's answer
# is pinned)
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law afw_malformed_unless_request:
  for +s: String
  for other: {String.eq(FAf.ffi(s), Wr.err("aux_fallback: malformed request")) == False{} : Bool}
  exs x: FAf.Req
  exs rest: String
  {(s, afw_req_fits(x)) == (afw_spell_req(x, rest), True{}) : String & Bool}

# LAW afw_tags_example: anchor: the bytes Rust sends and reads (purpose and selector the
# opaque 0): gate unset (0,0,0,T), session model (0,0,1,F): session (0,0,);
# another admitted (0,0,2,0,T): look up (1,0,0,); not admitted (0,0,2,0,F):
# fallback reason 0 (0,2,0,0,0,); settle a miss of reason 3 (1,1,0,0,0,3,7,):
# fallback reason 3 (2,0,0,3,); a hit of window 10 for 5 (1,1,0,0,1,10,5,)
# and of unknown window 0: routed (1,); of window 4 for 5: reason 5
# (2,0,0,5,); a pass of a shown key: substitution only, keys kept; a
# session pass: stay; unknown request, selector, gate, lookup, route and
# Bool tags are malformed; a request with input left over is refused
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, a reversed allowedModels flag, an unknown tag read as a known
#   one, the two error texts swapped
law afw_tags_example:
  {[FAf.ffi("0,0,0,T"), FAf.ffi("0,0,1,F"), FAf.ffi("0,0,2,0,T"), FAf.ffi("0,0,2,0,F"), FAf.ffi("1,1,0,0,0,3,7,"), FAf.ffi("1,1,0,0,1,10,5,"), FAf.ffi("1,1,0,0,1,0,5,"), FAf.ffi("1,1,0,0,1,4,5,"), FAf.ffi("2,2,1,2,3,1,1,2,3,"), FAf.ffi("2,0,0,"), FAf.ffi("3,"), FAf.ffi("0,0,3,T"), FAf.ffi("1,2,0,"), FAf.ffi("1,1,0,0,2,5,5,"), FAf.ffi("2,3,0,"), FAf.ffi("0,0,0,X"), FAf.ffi("0,0,0,Tx"), FAf.ffi("1,1,0,0,1,10,5,,")] == ["0,0,", "0,0,", "1,0,0,", "0,2,0,0,0,", "2,0,0,3,", "1,", "1,", "2,0,0,5,", "1,2,1,2,3,1,1,2,3,", "1,0,0,", Wr.err("aux_fallback: malformed request"), Wr.err("aux_fallback: malformed request"), Wr.err("aux_fallback: malformed request"), Wr.err("aux_fallback: malformed request"), Wr.err("aux_fallback: malformed request"), Wr.err("aux_fallback: malformed request"), Wr.err("aux_fallback: input left over"), Wr.err("aux_fallback: input left over")] : List<&2, String>}
