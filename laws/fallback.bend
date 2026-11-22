# eukhe: the laws of area fallback

import Base
import ../bend/fallback.bend as Fb
import ../bend/ffi_fallback.bend as FFb
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (A1) A failed model hands the run to another model the user is signed in to
# ---------------------------------------------------------------------------
# Owner decision of 2026-11-17: a run that stops to ask hands work back to
# a person; when its model cannot go on (its retries ran out, its login
# expired, its usage limit holds, or no model was chosen) it goes on with
# another model the user configured and is signed in to, and the end of
# the run reports the switch. Owner decision of 2026-11-21: attention is
# the one scarce input; past the configured models the run goes on with
# the default model of every other provider the user is signed in to, and
# a run with no model left ends with a report that names the cause. Owner
# decision of 2026-11-22: the configured models are those configured to do
# the run's work (`enabledModels`, then the chat, image, subagent, worker
# and gateway roles); a model configured only for a side job (memory,
# summaries, `rlm.query`, titles, judgments, translation) is none.
# bend/fallback.bend: the choice. It runs as the compiled core by
# bend/ffi_fallback.bend (eukhe-bend rules/fallback.rs), asked by
# eukhe-core durable/models/provider.rs when a request gives up. Every
# input is free: any failure, any configured candidates and signed-in
# defaults in any order, any tried models.
#
# R1: a retryable failure keeps the run on its model while the run's
#     retries remain (the n-th failure in a row with n <= retries), with
#     any candidates.
# R2: past that, the run switches to the first configured candidate in
#     order that it has not tried, whatever the signed-in defaults; never
#     to a tried model, never past an untried one.
# R5: with every configured candidate tried, the run switches to the
#     first signed-in default in order that it has not tried.
# R3: with every candidate and every default tried, a usage limit holds
#     until its reset; every other failure ends, and the end carries that
#     failure: the cause the run's end report names.
# R4: the entry answers each request Rust writes (every number within the
#     wire) with the model's choice, reads exactly the request and nothing
#     after it, and answers any other input with the exact error form
#     `E fallback: malformed request`.
#
# Not pinned here, the Rust tests pin it:
# - which models Rust offers: the models configured to do the work whose
#   provider has credentials, then the default model of each other
#   provider with credentials the allowlist permits (eukhe-core
#   durable/models/fallback.rs
#   `candidates_are_the_work_models_with_credentials`,
#   `a_side_jobs_model_is_a_candidate_only_when_it_also_does_work`,
#   `defaults_are_the_signed_in_providers_default_models`);
# - what it does with the choice and the report of a switch or an end
#   (eukhe-core durable/models/provider_tests.rs
#   `a_failed_model_hands_the_request_to_the_next_configured_model`,
#   `an_expired_login_hands_the_request_to_a_signed_in_model`,
#   `an_expired_login_goes_on_with_a_signed_in_providers_default`,
#   `an_expired_login_goes_on_with_a_default_never_the_memory_model`,
#   `an_expired_login_with_no_model_left_ends_with_the_login_report`; the
#   report itself: durable/models/fallback.rs
#   `an_end_on_a_login_names_the_login_command`);
# - that a login a run found unusable stays so for the rest of the run:
#   later requests start on the model the run moved to and never refresh
#   it again (provider_tests.rs `a_dead_login_is_not_tried_again_in_the_run`,
#   `a_dead_login_is_never_refreshed_until_a_new_login`).

# Spec helpers
# ------------

# R2: m is among xs
def fb_in(+m: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Nat.is_eq(m, x), fb_in(m, t))

# R2, R3: every item of xs is among the tried models
def fb_all_in(xs: List<&2, Nat>, +tried: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(fb_in(x, tried), fb_all_in(t, tried))

# R1: the failure keeps the run on its model: a retryable failure while
# the run's retries remain
def fb_keeps(k: Fb.Why) -> Bool:
  match k:
    case Fb.Failed{n, retries}:
      Nat.is_le(n, retries)
    case Fb.Login{}:
      False{}
    case Fb.Quota{until}:
      False{}
    case Fb.Unset{}:
      False{}

# R3: the failure is a usage limit
def fb_quota(k: Fb.Why) -> Bool:
  match k:
    case Fb.Failed{n, retries}:
      False{}
    case Fb.Login{}:
      False{}
    case Fb.Quota{until}:
      True{}
    case Fb.Unset{}:
      False{}

# R4: the Nats of a failure: 0, n, retries | 1 | 2, until | 3, then rest
def fb_why_nats(k: Fb.Why, rest: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case Fb.Failed{n, retries}:
      0n <> n <> retries <> rest
    case Fb.Login{}:
      1n <> rest
    case Fb.Quota{until}:
      2n <> until <> rest
    case Fb.Unset{}:
      3n <> rest

# R4: the Nats of a request: the failure, the count of candidates, the
# candidates, the count of signed-in defaults, the defaults, the tried
# models
def fb_nats(x: Fb.In) -> List<&2, Nat>:
  match x:
    case Fb.In{k, +cands, +defaults, tried}:
      fb_why_nats(k, List.length(&2, Nat, cands) <> List.append(&2, Nat, cands, List.length(&2, Nat, defaults) <> List.append(&2, Nat, defaults, tried)))

# R4: the spelling of a request: its Nats as one list, then rest
def fb_req(x: Fb.In, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, fb_nats(x), rest)

# R4: every number of a request fits the wire
def fb_fits(+x: Fb.In) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, fb_nats(x))), LawsBase.wire_nats_fit(fb_nats(x)))

# R4: Nats spelled one after another, then rest
def fb_spell(xs: List<&2, Nat>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      Wr.put_nat(x, fb_spell(t, rest))

# R4: the spelling of a reply: 0 | 1, m | 2, until | 3, then the Nats of
# the failure the end carries
def fb_reply(c: Fb.Choice) -> String:
  match c:
    case Fb.Keep{}:
      Wr.put_nat(0n, "")
    case Fb.Switch{m}:
      Wr.put_nat(1n, Wr.put_nat(m, ""))
    case Fb.Hold{until}:
      Wr.put_nat(2n, Wr.put_nat(until, ""))
    case Fb.End{k}:
      Wr.put_nat(3n, fb_spell(fb_why_nats(k, []), ""))

# Laws: the choice (R1-R3, R5)
# ----------------------------

# LAW fallback_keeps_within_retries (R1): the n-th retryable failure in a
# row with n <= retries keeps the run on its model, whatever the
# candidates, the signed-in defaults and the tried models
# EXCLUDES: a switch while the run's own retries remain (one blip moves
#   the run), retries counted one short (n < retries); a keep past them
#   is fallback_switches_first_untried's and fallback_ends_when_none_left's
law fallback_keeps_within_retries:
  for +n: Nat
  for +retries: Nat
  for +cands: List<&2, Nat>
  for +defaults: List<&2, Nat>
  for +tried: List<&2, Nat>
  for h: {Nat.is_le(n, retries) == True{} : Bool}
  {Fb.choose(Fb.In{Fb.Failed{n, retries}, cands, defaults, tried}) == Fb.Keep{} : Fb.Choice}

# LAW fallback_switches_first_untried (R2): past a keep, with candidates
# p, then c, then any more, where every model of p was tried and c was
# not, the run switches to c, whatever the signed-in defaults
# EXCLUDES: a switch to a tried model (back to the model that failed), a
#   switch past the first untried candidate (the user's order ignored), a
#   switch to a model outside the candidates, a signed-in default taken
#   before an untried configured model, an end or a hold while a
#   candidate is untried
law fallback_switches_first_untried:
  for +k: Fb.Why
  for hk: {fb_keeps(k) == False{} : Bool}
  for +p: List<&2, Nat>
  for +c: Nat
  for +rest: List<&2, Nat>
  for +defaults: List<&2, Nat>
  for +tried: List<&2, Nat>
  for hp: {fb_all_in(p, tried) == True{} : Bool}
  for hc: {fb_in(c, tried) == False{} : Bool}
  {Fb.choose(Fb.In{k, List.append(&2, Nat, p, c <> rest), defaults, tried}) == Fb.Switch{c} : Fb.Choice}

# LAW fallback_switches_first_untried_default (R5): past a keep, with
# every configured candidate tried and signed-in defaults p, then d, then
# any more, where every model of p was tried and d was not, the run
# switches to d
# EXCLUDES: an end or a hold while a signed-in default is untried (a
#   signed-in provider left unused, the run handed to a person), a switch
#   to a tried default, a switch past the first untried default, a switch
#   to a model outside the defaults
law fallback_switches_first_untried_default:
  for +k: Fb.Why
  for hk: {fb_keeps(k) == False{} : Bool}
  for +cands: List<&2, Nat>
  for +p: List<&2, Nat>
  for +d: Nat
  for +rest: List<&2, Nat>
  for +tried: List<&2, Nat>
  for hcs: {fb_all_in(cands, tried) == True{} : Bool}
  for hp: {fb_all_in(p, tried) == True{} : Bool}
  for hd: {fb_in(d, tried) == False{} : Bool}
  {Fb.choose(Fb.In{k, cands, List.append(&2, Nat, p, d <> rest), tried}) == Fb.Switch{d} : Fb.Choice}

# LAW fallback_quota_holds_when_none_left (R3): a usage limit with every
# candidate and every signed-in default tried holds the run until the
# reset
# EXCLUDES: a usage limit that ends the run when it could wait, a hold to
#   another time than the reset
law fallback_quota_holds_when_none_left:
  for +until: Nat
  for +cands: List<&2, Nat>
  for +defaults: List<&2, Nat>
  for +tried: List<&2, Nat>
  for h: {fb_all_in(cands, tried) == True{} : Bool}
  for hd: {fb_all_in(defaults, tried) == True{} : Bool}
  {Fb.choose(Fb.In{Fb.Quota{until}, cands, defaults, tried}) == Fb.Hold{until} : Fb.Choice}

# LAW fallback_ends_when_none_left (R3): any other failure past a keep,
# with every candidate and every signed-in default tried, ends, and the
# end carries that failure (the cause the end report names)
# EXCLUDES: a hold with no reset to wait for, a switch back to a tried
#   model, a keep past the run's retries, an end that names another cause
#   (an expired login reported as a failing model, or as no model chosen)
law fallback_ends_when_none_left:
  for +k: Fb.Why
  for hk: {fb_keeps(k) == False{} : Bool}
  for hq: {fb_quota(k) == False{} : Bool}
  for +cands: List<&2, Nat>
  for +defaults: List<&2, Nat>
  for +tried: List<&2, Nat>
  for h: {fb_all_in(cands, tried) == True{} : Bool}
  for hd: {fb_all_in(defaults, tried) == True{} : Bool}
  {Fb.choose(Fb.In{k, cands, defaults, tried}) == Fb.End{k} : Fb.Choice}

# LAW fallback_example (R1-R3, R5): anchor: a second failure of two
# retries keeps; a third switches past the tried model 4 to 7 before the
# default 9; an expired login with no candidate ends with the login; a
# usage limit with its one candidate tried holds until 99; no model chosen
# switches to the first candidate; an expired login with its configured
# model tried skips that model among the defaults and takes 6; a third
# failure with nothing left ends with that failure
# EXCLUDES: candidates read from the end, a keep at n = retries + 1, a
#   default before a configured model
law fallback_example:
  {[Fb.choose(Fb.In{Fb.Failed{2n, 2n}, [4n, 7n], [], [0n]}), Fb.choose(Fb.In{Fb.Failed{3n, 2n}, [4n, 7n], [9n], [0n, 4n]}), Fb.choose(Fb.In{Fb.Login{}, [], [], [0n]}), Fb.choose(Fb.In{Fb.Quota{99n}, [5n], [], [0n, 5n]}), Fb.choose(Fb.In{Fb.Unset{}, [3n, 1n], [], []}), Fb.choose(Fb.In{Fb.Login{}, [4n], [4n, 6n], [0n, 4n]}), Fb.choose(Fb.In{Fb.Failed{3n, 2n}, [], [], [0n]})] == [Fb.Keep{}, Fb.Switch{7n}, Fb.End{Fb.Login{}}, Fb.Hold{99n}, Fb.Switch{3n}, Fb.Switch{6n}, Fb.End{Fb.Failed{3n, 2n}}] : List<&2, Fb.Choice>}

# Laws: the entry (R4)
# --------------------

# LAW fallback_entry_parses (R4): the Nats of every request parse back to
# that request
# EXCLUDES: a field lost, swapped or defaulted on the way in, candidates,
#   signed-in defaults and tried models cut at the wrong place
law fallback_entry_parses:
  for +x: Fb.In
  {FFb.parse(fb_nats(x)) == Some{x} : Maybe<&2, Fb.In>}

# LAW fallback_entry_is_model (R4): the entry answers every request Rust
# spells, every number within the wire, with the model's choice, spelled
# EXCLUDES: a request misread, a default, another reply spelling
law fallback_entry_is_model:
  for +x: Fb.In
  for h: {fb_fits(x) == True{} : Bool}
  {FFb.ffi(fb_req(x, "")) == fb_reply(Fb.choose(x)) : String}

# LAW fallback_entry_exact (R4): every input the entry does not answer with
# the error form is a spelled request, every number of it within the wire
# EXCLUDES: an answer for input that is no request (an unknown failure
#   tag, a count past the items, input left over), an answer for a number
#   past the wire (a reset of 15 digits read as a hold)
law fallback_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FFb.ffi(s)) == False{} : Bool}
  exs x: Fb.In
  {s == fb_req(x, "") : String} & {fb_fits(x) == True{} : Bool}

# LAW fallback_entry_refuses (R4): every error the entry answers is exactly
# `E fallback: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law fallback_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FFb.ffi(s)) == True{} : Bool}
  {FFb.ffi(s) == Wr.err("fallback: malformed request") : String}

# LAW fallback_entry_example (R4): anchor: the wire strings Rust sends and
# the replies it reads (keep; switch; hold; an end that carries the
# expired login; no model chosen; a switch to a signed-in default; an end
# that carries the failures in a row); an unknown failure tag, a
# candidate count past the items, a default count past the items, input
# left over
# EXCLUDES: another request or reply spelling
law fallback_entry_example:
  {[FFb.ffi("6,0,1,1,1,0,0,"), FFb.ffi("7,0,3,1,2,7,0,0,"), FFb.ffi("6,2,99,1,5,0,5,"), FFb.ffi("4,1,0,0,0,"), FFb.ffi("4,3,1,7,0,"), FFb.ffi("5,1,0,1,4,0,"), FFb.ffi("6,0,2,1,0,0,0,"), FFb.ffi("2,4,0,"), FFb.ffi("3,1,5,0,"), FFb.ffi("4,1,0,5,0,"), FFb.ffi("4,1,0,0,0,x")] == ["0,", "1,7,", "2,99,", "3,1,", "1,7,", "1,4,", "3,0,2,1,", Wr.err("fallback: malformed request"), Wr.err("fallback: malformed request"), Wr.err("fallback: malformed request"), Wr.err("fallback: malformed request")] : List<&2, String>}
