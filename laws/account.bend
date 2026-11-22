# eukhe: the laws of area account

import Base
import ../bend/account.bend as Ac
import ../bend/ffi_account.bend as FAc
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (A1) A limited account hands the run to another account of its provider
# -----------------------------------------------------------------------
# Owner decision of 2026-11-21: a provider holds several logins
# (accounts); a session sticks to one; when it hits a usage or rate
# limit, or its login cannot refresh, the run goes on with another
# account of the same provider and the same model before any other model,
# and with every account limited it waits for the earliest reset within
# the run's wait limit, else hands the run to its model fallback.
# bend/account.bend: the choice. It runs as the compiled core by
# bend/ffi_account.bend (eukhe-bend rules/account.rs), asked by eukhe-core
# durable/models/accounts.rs when a session first sends to a provider
# and when a request's account fails. Every input is free: any clock, any
# wait limit, any marks in any order.
#
# R1: the run goes on with the first account usable at now (Free, or a
#     limit that reset: Until{t} with t <= now), whatever the wait.
# R2: with none usable, the earliest limit decides (the first account
#     with it on a tie): the run waits for it when the run may still wait
#     and it resets within the wait limit;
# R3: else it hands the run on with that account and that reset (the
#     model fallback's usage limit);
# R4: with none usable and none limited (every login dead, or no
#     account), no login is left.
# R5: the entry answers each request Rust writes (every number within the
#     wire) with the model's choice, reads exactly the request and nothing
#     after it, and answers any other input with the exact error form
#     `E account: malformed request`.
#
# Not pinned here, the Rust tests pin it:
# - the marks Rust gathers (a limit the provider reports, a refresh that
#   failed) and the account order (eukhe-core auth/accounts.rs
#   `a_login_adds_or_replaces_by_identity`; durable/models/accounts.rs
#   `every_account_failing_waits_or_hands_on`);
# - that a session sticks to one account until it fails
#   (durable/models/accounts.rs
#   `a_session_keeps_its_account_until_it_fails`);
# - that the account step runs before the model fallback and a usable
#   sibling account never reaches it, and the report of a switch
#   (eukhe-core durable/models/provider_tests.rs
#   `a_limited_account_hands_the_request_to_its_sibling`,
#   `every_account_limited_hands_the_request_to_the_model_fallback`;
#   eukhe-cli tests/multi_account_e2e.rs).

# Spec helpers
# ------------

# R1: the account can serve at now
def ac_usable(+now: Nat, m: Ac.Mark) -> Bool:
  match m:
    case Ac.Free{}:
      True{}
    case Ac.Until{t}:
      Bool.not(Nat.is_lt(now, t))
    case Ac.Dead{}:
      False{}

# R1: no account of ms can serve at now
def ac_none_usable(+now: Nat, ms: List<&2, Ac.Mark>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      Bool.and(Bool.not(ac_usable(now, m)), ac_none_usable(now, t))

# R2, R3: every account of ms is dead or limited past e
def ac_all_after(+e: Nat, ms: List<&2, Ac.Mark>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      match m:
        case Ac.Free{}:
          False{}
        case Ac.Until{u}:
          Bool.and(Nat.is_lt(e, u), ac_all_after(e, t))
        case Ac.Dead{}:
          ac_all_after(e, t)

# R2, R3: every account of ms is dead or limited until e or later
def ac_all_from(+e: Nat, ms: List<&2, Ac.Mark>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      match m:
        case Ac.Free{}:
          False{}
        case Ac.Until{u}:
          Bool.and(Nat.is_le(e, u), ac_all_from(e, t))
        case Ac.Dead{}:
          ac_all_from(e, t)

# R4: every login of ms is dead
def ac_all_dead(ms: List<&2, Ac.Mark>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      match m:
        case Ac.Free{}:
          False{}
        case Ac.Until{u}:
          False{}
        case Ac.Dead{}:
          ac_all_dead(t)

# R2, R3: the run may still wait and e resets within the wait limit
def ac_may_wait(+now: Nat, +cap: Nat, +waits: Nat, +e: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, waits), Bool.not(Nat.is_lt(Nat.add(now, cap), e)))

# R5: the Nats of a mark: 0 | 1, t | 2, then rest
def ac_mark_nats(m: Ac.Mark, rest: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case Ac.Free{}:
      0n <> rest
    case Ac.Until{t}:
      1n <> t <> rest
    case Ac.Dead{}:
      2n <> rest

# R5: the Nats of the marks in order
def ac_marks_nats(ms: List<&2, Ac.Mark>) -> List<&2, Nat>:
  match ms:
    case Nil{}:
      []
    case m <> t:
      ac_mark_nats(m, ac_marks_nats(t))

# R5: the Nats of a request: now, cap, waits, then the marks
def ac_nats(x: Ac.In) -> List<&2, Nat>:
  match x:
    case Ac.In{now, cap, waits, ms}:
      now <> cap <> waits <> ac_marks_nats(ms)

# R5: the spelling of a request: its Nats as one list, then rest
def ac_req(x: Ac.In, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, ac_nats(x), rest)

# R5: every number of a request fits the wire
def ac_fits(+x: Ac.In) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ac_nats(x))), LawsBase.wire_nats_fit(ac_nats(x)))

# R5: the spelling of a reply: 0, a | 1, a, until | 2, a, until | 3
def ac_reply(c: Ac.Choice) -> String:
  match c:
    case Ac.Use{a}:
      Wr.put_nat(0n, Wr.put_nat(a, ""))
    case Ac.Hold{a, until}:
      Wr.put_nat(1n, Wr.put_nat(a, Wr.put_nat(until, "")))
    case Ac.Quota{a, until}:
      Wr.put_nat(2n, Wr.put_nat(a, Wr.put_nat(until, "")))
    case Ac.Login{}:
      Wr.put_nat(3n, "")

# Laws: the choice (R1-R4)
# ------------------------

# LAW account_uses_first_usable (R1): with accounts p, then m, then any
# more, where no account of p can serve at now and m can, the run goes on
# with m (its place: the length of p), whatever the wait limit and the
# waits left
# EXCLUDES: a limited or dead account used while one can serve, an
#   account past the first usable one (the user's order ignored), a limit
#   that reset still treated as limited (t <= now), a wait or a hand-off
#   while an account can serve, a place counted from 1
law account_uses_first_usable:
  for +now: Nat
  for +cap: Nat
  for +waits: Nat
  for +p: List<&2, Ac.Mark>
  for +m: Ac.Mark
  for +rest: List<&2, Ac.Mark>
  for hp: {ac_none_usable(now, p) == True{} : Bool}
  for hm: {ac_usable(now, m) == True{} : Bool}
  {Ac.choose(Ac.In{now, cap, waits, List.append(&2, Ac.Mark, p, m <> rest)}) == Ac.Use{List.length(&2, Ac.Mark, p)} : Ac.Choice}

# LAW account_waits_for_earliest (R2): with accounts p, then one limited
# until e (past now), then any more, where every account of p is dead or
# limited past e and every later one dead or limited until e or later,
# the run waits for that account until e when it may still wait and e is
# within the wait limit
# EXCLUDES: a wait for a later reset than the earliest, the last account
#   of a tie taken over the first, a wait past the wait limit or with no
#   waits left (that is account_hands_on_past_wait's), a hand-off while
#   it may wait, a wait for a dead login
law account_waits_for_earliest:
  for +now: Nat
  for +cap: Nat
  for +waits: Nat
  for +p: List<&2, Ac.Mark>
  for +e: Nat
  for +rest: List<&2, Ac.Mark>
  for he: {Nat.is_lt(now, e) == True{} : Bool}
  for hp: {ac_all_after(e, p) == True{} : Bool}
  for hr: {ac_all_from(e, rest) == True{} : Bool}
  for hw: {ac_may_wait(now, cap, waits, e) == True{} : Bool}
  {Ac.choose(Ac.In{now, cap, waits, List.append(&2, Ac.Mark, p, Ac.Until{e} <> rest)}) == Ac.Hold{List.length(&2, Ac.Mark, p), e} : Ac.Choice}

# LAW account_hands_on_past_wait (R3): the same accounts, when the run may
# not wait (no waits left, or e past the wait limit), hand the run on with
# that account and its reset e
# EXCLUDES: a wait with no waits left or past the wait limit (a run that
#   stalls for hours), a hand-off that names a later reset or another
#   account, a login failure reported while a limit holds
law account_hands_on_past_wait:
  for +now: Nat
  for +cap: Nat
  for +waits: Nat
  for +p: List<&2, Ac.Mark>
  for +e: Nat
  for +rest: List<&2, Ac.Mark>
  for he: {Nat.is_lt(now, e) == True{} : Bool}
  for hp: {ac_all_after(e, p) == True{} : Bool}
  for hr: {ac_all_from(e, rest) == True{} : Bool}
  for hw: {ac_may_wait(now, cap, waits, e) == False{} : Bool}
  {Ac.choose(Ac.In{now, cap, waits, List.append(&2, Ac.Mark, p, Ac.Until{e} <> rest)}) == Ac.Quota{List.length(&2, Ac.Mark, p), e} : Ac.Choice}

# LAW account_login_when_all_dead (R4): with every login dead (or no
# account), no login is left
# EXCLUDES: a dead login used again, a wait or a hand-off with a reset no
#   account has
law account_login_when_all_dead:
  for +now: Nat
  for +cap: Nat
  for +waits: Nat
  for +ms: List<&2, Ac.Mark>
  for h: {ac_all_dead(ms) == True{} : Bool}
  {Ac.choose(Ac.In{now, cap, waits, ms}) == Ac.Login{} : Ac.Choice}

# LAW account_example (R1-R4): anchor: at 10, a dead login and a limit
# until 50 skip to the free third account; a limit until 10 has reset;
# limits until 40, 30, 30 wait for the first 30 within a wait limit of
# 25; the same with no waits left hand on with it; a wait limit of 5
# hands on; two dead logins leave none; no account leaves none
# EXCLUDES: a limit at its reset read as holding, the last of a tie, a
#   wait with no waits left
law account_example:
  {[Ac.choose(Ac.In{10n, 25n, 1n, [Ac.Dead{}, Ac.Until{50n}, Ac.Free{}]}), Ac.choose(Ac.In{10n, 25n, 1n, [Ac.Dead{}, Ac.Until{10n}]}), Ac.choose(Ac.In{10n, 25n, 1n, [Ac.Until{40n}, Ac.Until{30n}, Ac.Until{30n}]}), Ac.choose(Ac.In{10n, 25n, 0n, [Ac.Until{40n}, Ac.Until{30n}, Ac.Until{30n}]}), Ac.choose(Ac.In{10n, 5n, 3n, [Ac.Until{40n}, Ac.Dead{}]}), Ac.choose(Ac.In{10n, 25n, 1n, [Ac.Dead{}, Ac.Dead{}]}), Ac.choose(Ac.In{10n, 25n, 1n, []})] == [Ac.Use{2n}, Ac.Use{1n}, Ac.Hold{1n, 30n}, Ac.Quota{1n, 30n}, Ac.Quota{0n, 40n}, Ac.Login{}, Ac.Login{}] : List<&2, Ac.Choice>}

# Laws: the entry (R5)
# --------------------

# LAW account_entry_parses (R5): the Nats of every request parse back to
# that request
# EXCLUDES: a field lost, swapped or defaulted on the way in, a mark read
#   as another, marks cut short
law account_entry_parses:
  for +x: Ac.In
  {FAc.parse(ac_nats(x)) == Some{x} : Maybe<&2, Ac.In>}

# LAW account_entry_is_model (R5): the entry answers every request Rust
# spells, every number within the wire, with the model's choice, spelled
# EXCLUDES: a request misread, a default, another reply spelling
law account_entry_is_model:
  for +x: Ac.In
  for h: {ac_fits(x) == True{} : Bool}
  {FAc.ffi(ac_req(x, "")) == ac_reply(Ac.choose(x)) : String}

# LAW account_entry_exact (R5): every input the entry does not answer with
# the error form is a spelled request, every number of it within the wire
# EXCLUDES: an answer for input that is no request (an unknown mark tag, a
#   limit with no reset, a request with no waits, input left over), an
#   answer for a number past the wire
law account_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FAc.ffi(s)) == False{} : Bool}
  exs x: Ac.In
  {s == ac_req(x, "") : String} & {ac_fits(x) == True{} : Bool}

# LAW account_entry_refuses (R5): every error the entry answers is exactly
# `E account: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law account_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FAc.ffi(s)) == True{} : Bool}
  {FAc.ffi(s) == Wr.err("account: malformed request") : String}

# LAW account_entry_example (R5): anchor: the wire strings Rust sends and
# the replies it reads (use; wait; hand-off; no login left); an unknown
# mark tag, a limit with no reset, a request with no waits, input left
# over
# EXCLUDES: another request or reply spelling
law account_entry_example:
  {[FAc.ffi("5,10,25,1,2,0,"), FAc.ffi("7,10,25,1,1,40,1,30,"), FAc.ffi("7,10,25,0,1,40,1,30,"), FAc.ffi("4,10,25,1,2,"), FAc.ffi("4,10,25,1,3,"), FAc.ffi("4,10,25,1,1,"), FAc.ffi("2,10,25,"), FAc.ffi("4,10,25,1,0,x")] == ["0,1,", "1,1,30,", "2,1,30,", "3,", Wr.err("account: malformed request"), Wr.err("account: malformed request"), Wr.err("account: malformed request"), Wr.err("account: malformed request")] : List<&2, String>}
