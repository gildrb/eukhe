# eukhe: the laws of area default_model

import Base
import ../bend/default_model.bend as Dm
import ../bend/ffi_default_model.bend as FDm
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (H4) The saved default model
# ----------------------------
# bend/default_model.bend: the session-model resolution at open (audit
# finding H4). Sources: the header of bend/default_model.bend;
# crates/eukhe-core/src/models/resolver.rs `DefaultMiss`,
# `saved_default_facts`, `resolve_default`, `saved_default_miss`;
# crates/eukhe-core/src/durable/models.rs `Substitution`, `resolve` and
# its regression tests (audit H4). omp (packages/coding-agent/src/config/
# model-resolver.ts `findInitialModel`) takes the saved default when the
# registry has it and else the first model with a key, in silence; its
# `restoreModelFromSession` names the reason it falls back ("model no
# longer exists", "no API key available"). Eukhe's audit H4 fix keeps
# omp's order and makes every move past the saved default name it (R6)
# and never moves past an unkeyed one (R4): the Rust doc comments are the
# requirement where they differ from omp.
#
# Requirements:
#   R1  the request and every part of the reply read back (wire section)
#   R2  a well-formed request answers the resolver's answer, spelled
#   R3  a malformed request, or a request with input left over, answers
#       the error form, never a model
#   R4  the checks of a saved default, in this order: the catalog, the
#       credentials, the scope (`saved_default_miss`); with nothing saved
#       the chain's pick runs, or no model; a saved default that fails the
#       catalog or the scope gives way to the chain's pick, else is the
#       typed error; one that fails the credentials is the typed error,
#       never another provider (`resolve_default` doc)
#   R5  a session opens on the model the resolver answers; with no model
#       it opens with none (`OpenModel`, header lines 26-28)
#   R6  a saved default that does not run is named, once, with the first
#       check it fails ("the startup chain never moves past the saved
#       default in silence", `DefaultMiss` doc)
#   R7  no notice when the saved default runs or nothing is saved
#   A1  a usable saved default's answer does not depend on the chain's
#       pick (a catalog refresh never moves it)
#
# Trusted code the laws below read through: Dm.Session.run and
# Dm.Session.notes (the session's two fields), Dm.open, Dm.resolve.

# the reason r is the first check a saved default fails, with the facts
# cat (in the catalog), key (its provider has credentials) and out (a set
# scope leaves it out): the catalog fails; else the credentials fail; else
# the scope fails
def dm_fails_first(r: Dm.Reason, cat: Bool, key: Bool, out: Bool) -> Bool:
  match r:
    case Dm.NotInCatalog{}:
      Bool.not(cat)
    case Dm.NoCredentials{}:
      Bool.and(cat, Bool.not(key))
    case Dm.NotInScope{}:
      Bool.and(cat, Bool.and(key, out))

# LAW default_miss_named_once (R6): a saved default m that fails a check
# opens a session whose notices are exactly one: m with the first check it
# fails (the catalog, then the credentials, then the scope), whatever the
# chain picks and whatever the facts after that check
# EXCLUDES: a silent swap or refusal, a notice given twice, a notice that
#   names the replacement or another model, a later check named in place
#   of the first one that fails (a scope miss reported for a model the
#   catalog lacks)
law default_miss_named_once:
  for m: Nat
  for cat: Bool
  for key: Bool
  for out: Bool
  for next: Dm.Next
  for r: Dm.Reason
  for fails: {dm_fails_first(r, cat, key, out) == True{} : Bool}
  {Dm.Session.notes(Dm.open(Dm.resolve(Dm.In{Dm.Default{m}, cat, key, out, next}))) == [Dm.K{m, r}] : List<&2, Dm.Key>}

# LAW default_quiet_when_honoured (R7): a session that opens on the saved
# default has no notice
# EXCLUDES: a notice shown for a saved default that runs
law default_quiet_when_honoured:
  for x: Dm.In
  for h: {Dm.Session.run(Dm.open(Dm.resolve(x))) == Dm.On{Dm.Saved{}} : Dm.Run}
  {Dm.Session.notes(Dm.open(Dm.resolve(x))) == Nil{} : List<&2, Dm.Key>}

# LAW default_quiet_when_unset (R7): with no saved default the session has no notice
law default_quiet_when_unset:
  for cat: Bool
  for key: Bool
  for out: Bool
  for next: Dm.Next
  {Dm.Session.notes(Dm.open(Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, next}))) == Nil{} : List<&2, Dm.Key>}

# LAW default_session_runs_answer (R5): an answer with a model (the saved
# default or another one, kept or swapped) opens the session on that model
# EXCLUDES: a swap opened on the saved default, the chain's pick replaced
#   by another model on the way to the session, a model answer opened idle
law default_session_runs_answer:
  for p: Dm.Pick
  for s: Dm.Sub
  {Dm.Session.run(Dm.open(Dm.Runs{p, s})) == Dm.On{p} : Dm.Run}

# LAW default_session_idle_without_model (R5): no model, and the typed
# error, open the session with no model
# EXCLUDES: a refused saved default, or an empty chain, opened on a model
law default_session_idle_without_model:
  for k: Dm.Key
  {Dm.Session.run(Dm.open(Dm.Nothing{})) == Dm.Idle{} : Dm.Run} & {Dm.Session.run(Dm.open(Dm.Refused{k})) == Dm.Idle{} : Dm.Run}

# LAW default_unkeyed_never_moves (R4): a saved default the catalog has,
# whose provider has no credentials, opens the session with no model,
# whatever the scope and the chain's pick: no other provider runs in its
# place (a saved default the catalog lacks fails the catalog check first
# and gives way to the chain's pick: default_uncatalogued_swaps)
# EXCLUDES: a move to another provider for an unkeyed saved default
law default_unkeyed_never_moves:
  for m: Nat
  for out: Bool
  for next: Dm.Next
  {Dm.Session.run(Dm.open(Dm.resolve(Dm.In{Dm.Default{m}, True{}, False{}, out, next}))) == Dm.Idle{} : Dm.Run}

# The laws below pin every answer of the resolver (Dm.resolve, the Rust
# `resolve_session_model` with no requested model), case by case (R4):
# nothing saved; the catalog, the credentials and the scope, in this
# order; the chain's pick or none.

# LAW default_unset_runs_pick: with nothing saved the chain's pick runs, with nothing to say
# EXCLUDES: a notice or a substitution invented for an unset default, the
#   chain's pick ignored
law default_unset_runs_pick:
  for cat: Bool
  for key: Bool
  for out: Bool
  for n: Nat
  {Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, Dm.Next{n}}) == Dm.Runs{Dm.Other{n}, Dm.Kept{}} : Dm.Res}

# LAW default_unset_without_pick: with nothing saved and no model to pick there is no model, and no
# error
# EXCLUDES: a typed error for an unset default
law default_unset_without_pick:
  for cat: Bool
  for key: Bool
  for out: Bool
  {Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, Dm.NoNext{}}) == Dm.Nothing{} : Dm.Res}

# LAW default_usable_runs: a saved default in the catalog, with credentials and in the scope,
# runs, with nothing to say
# EXCLUDES: a usable saved default replaced by the chain's pick
law default_usable_runs:
  for m: Nat
  for next: Dm.Next
  {Dm.resolve(Dm.In{Dm.Default{m}, True{}, True{}, False{}, next}) == Dm.Runs{Dm.Saved{}, Dm.Kept{}} : Dm.Res}

# LAW default_uncatalogued_swaps: a saved default the catalog lacks gives way to the chain's pick,
# which names it with the reason "not in the catalog"
# EXCLUDES: a wrong reason, a silent substitution, the credentials or
#   the scope checked before the catalog
law default_uncatalogued_swaps:
  for m: Nat
  for key: Bool
  for out: Bool
  for n: Nat
  {Dm.resolve(Dm.In{Dm.Default{m}, False{}, key, out, Dm.Next{n}}) == Dm.Runs{Dm.Other{n}, Dm.Swapped{Dm.K{m, Dm.NotInCatalog{}}}} : Dm.Res}

# LAW default_uncatalogued_refused: a saved default the catalog lacks, with no model to pick, is the
# typed error with the reason "not in the catalog"
# EXCLUDES: no model and no error (a silent idle session)
law default_uncatalogued_refused:
  for m: Nat
  for key: Bool
  for out: Bool
  {Dm.resolve(Dm.In{Dm.Default{m}, False{}, key, out, Dm.NoNext{}}) == Dm.Refused{Dm.K{m, Dm.NotInCatalog{}}} : Dm.Res}

# LAW default_unkeyed_refused: a saved default whose provider has no credentials is the typed
# error with the reason "no credentials", whatever the scope and the
# chain's pick
# EXCLUDES: a move to another provider, a wrong reason
law default_unkeyed_refused:
  for m: Nat
  for out: Bool
  for next: Dm.Next
  {Dm.resolve(Dm.In{Dm.Default{m}, True{}, False{}, out, next}) == Dm.Refused{Dm.K{m, Dm.NoCredentials{}}} : Dm.Res}

# LAW default_unscoped_swaps: a saved default outside the set scope gives way to the chain's
# pick, which names it with the reason "not in the scope"
# EXCLUDES: a silent substitution, a wrong reason
law default_unscoped_swaps:
  for m: Nat
  for n: Nat
  {Dm.resolve(Dm.In{Dm.Default{m}, True{}, True{}, True{}, Dm.Next{n}}) == Dm.Runs{Dm.Other{n}, Dm.Swapped{Dm.K{m, Dm.NotInScope{}}}} : Dm.Res}

# LAW default_unscoped_refused: a saved default outside the set scope, with no model to pick, is
# the typed error with the reason "not in the scope"
# EXCLUDES: no model and no error
law default_unscoped_refused:
  for m: Nat
  {Dm.resolve(Dm.In{Dm.Default{m}, True{}, True{}, True{}, Dm.NoNext{}}) == Dm.Refused{Dm.K{m, Dm.NotInScope{}}} : Dm.Res}

# LAW default_catalog_change_keeps_choice: a new chain pick (a catalog refresh, another featured
# model) never changes the answer for a saved default that runs
# EXCLUDES: the featured or first available model replacing a usable
#   saved default, an answer that depends on the chain's pick
law default_catalog_change_keeps_choice:
  for m: Nat
  for n1: Nat
  for n2: Nat
  {Dm.resolve(Dm.In{Dm.Default{m}, True{}, True{}, False{}, Dm.Next{n1}}) == Dm.resolve(Dm.In{Dm.Default{m}, True{}, True{}, False{}, Dm.Next{n2}}) : Dm.Res}

# The wire codec of bend/ffi_default_model.bend (grammar: that file's
# header, crates/eukhe-bend/WIRE.md). R1: the request and every reply
# read back; R2: a well-formed request answers the resolver's answer
# (Dm.resolve), encoded; R3: a malformed or overlong request answers the
# error form, never a model. Every input is free.

# what fits the wire: every Nat at most 14 digits
def dmw_saved_fits(x: Dm.Saved) -> Bool:
  match x:
    case Dm.NoDefault{}:
      True{}
    case Dm.Default{m}:
      LawsBase.wire_fits(m)

def dmw_next_fits(x: Dm.Next) -> Bool:
  match x:
    case Dm.NoNext{}:
      True{}
    case Dm.Next{n}:
      LawsBase.wire_fits(n)

def dmw_in_fits(x: Dm.In) -> Bool:
  match x:
    case Dm.In{saved, cat, key, out, next}:
      Bool.and(dmw_saved_fits(saved), dmw_next_fits(next))

def dmw_key_fits(k: Dm.Key) -> Bool:
  match k:
    case Dm.K{m, r}:
      LawsBase.wire_fits(m)

def dmw_pick_fits(p: Dm.Pick) -> Bool:
  match p:
    case Dm.Saved{}:
      True{}
    case Dm.Other{n}:
      LawsBase.wire_fits(n)

def dmw_sub_fits(s: Dm.Sub) -> Bool:
  match s:
    case Dm.Kept{}:
      True{}
    case Dm.Swapped{k}:
      dmw_key_fits(k)

def dmw_res_fits(r: Dm.Res) -> Bool:
  match r:
    case Dm.Runs{p, s}:
      Bool.and(dmw_pick_fits(p), dmw_sub_fits(s))
    case Dm.Nothing{}:
      True{}
    case Dm.Refused{k}:
      dmw_key_fits(k)

# LAW dmw_reason_round_trip (R1): a reason reads back, and the rest is untouched
# EXCLUDES: one reason read as another
law dmw_reason_round_trip:
  for r: Dm.Reason
  for rest: String
  {FDm.get_reason(FDm.put_reason(r, rest)) == Wr.Got{r, rest} : Wr.Dec<Dm.Reason>}

# LAW dmw_saved_round_trip (R1): a saved default that fits reads back
# EXCLUDES: no default read as one, a misread model
law dmw_saved_round_trip:
  for +x: Dm.Saved
  for rest: String
  for h: {dmw_saved_fits(x) == True{} : Bool}
  {FDm.get_saved(FDm.put_saved(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Dm.Saved>}

# LAW dmw_next_round_trip (R1): the chain's pick that fits reads back
# EXCLUDES: no pick read as one, a misread model
law dmw_next_round_trip:
  for +x: Dm.Next
  for rest: String
  for h: {dmw_next_fits(x) == True{} : Bool}
  {FDm.get_next(FDm.put_next(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Dm.Next>}

# LAW dmw_in_round_trip (R1): a request that fits reads back
# EXCLUDES: a fact (catalog, credentials, scope) lost, swapped or misread
law dmw_in_round_trip:
  for +x: Dm.In
  for rest: String
  for h: {dmw_in_fits(x) == True{} : Bool}
  {FDm.get_in(FDm.put_in(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Dm.In>}

# LAW dmw_key_round_trip (R1): a notice's key that fits reads back
# EXCLUDES: the model or the reason lost or misread
law dmw_key_round_trip:
  for +k: Dm.Key
  for rest: String
  for h: {dmw_key_fits(k) == True{} : Bool}
  {FDm.get_key(FDm.put_key(k, rest)) == Wr.Got{k, rest} : Wr.Dec<Dm.Key>}

# LAW dmw_pick_round_trip (R1): a pick that fits reads back
# EXCLUDES: the saved default read as another model, or the reverse
law dmw_pick_round_trip:
  for +p: Dm.Pick
  for rest: String
  for h: {dmw_pick_fits(p) == True{} : Bool}
  {FDm.get_pick(FDm.put_pick(p, rest)) == Wr.Got{p, rest} : Wr.Dec<Dm.Pick>}

# LAW dmw_sub_round_trip (R1): a substitution that fits reads back
# EXCLUDES: a swap read as kept (a silent substitution), or the reverse
law dmw_sub_round_trip:
  for +s: Dm.Sub
  for rest: String
  for h: {dmw_sub_fits(s) == True{} : Bool}
  {FDm.get_sub(FDm.put_sub(s, rest)) == Wr.Got{s, rest} : Wr.Dec<Dm.Sub>}

# LAW dmw_res_round_trip (R1): the reply, a resolution that fits, reads back
# EXCLUDES: a refusal read as a run or as no model, a field lost
law dmw_res_round_trip:
  for +r: Dm.Res
  for rest: String
  for h: {dmw_res_fits(r) == True{} : Bool}
  {FDm.get_res(FDm.put_res(r, rest)) == Wr.Got{r, rest} : Wr.Dec<Dm.Res>}

# LAW dmw_answers (R2): a request the entry's own encoder writes, every
# number within the wire, answers the resolver's answer as the entry's own
# encoder spells it (the spelling Rust reads is dmw_ffi_answers_spelled's)
# EXCLUDES: an entry that resolves other than Dm.resolve, or drops a fact
#   on the way in
law dmw_answers:
  for +x: Dm.In
  for h: {dmw_in_fits(x) == True{} : Bool}
  {FDm.ffi(FDm.put_in(x, "")) == FDm.put_res(Dm.resolve(x), "") : String}

# LAW dmw_left_over (R3): a request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law dmw_left_over:
  for +x: Dm.In
  for c: Char
  for rest: String
  for h: {dmw_in_fits(x) == True{} : Bool}
  {FDm.ffi(FDm.put_in(x, SCon{c, rest})) == Wr.err("default_model: input left over") : String}

# LAW dmw_reason_example (R1): anchor: the reasons' tags (0 not in the catalog | 1 no
# credentials | 2 not in the scope)
# EXCLUDES: tags in another order than the grammar's
law dmw_reason_example:
  {FDm.put_reason(Dm.NotInCatalog{}, FDm.put_reason(Dm.NoCredentials{}, FDm.put_reason(Dm.NotInScope{}, ""))) == "0,1,2," : String}

# LAW dmw_saved_example (R1): anchor and witness: a saved default is 0 (none) or 1, then it
# EXCLUDES: a vacuous dmw_saved_round_trip, another spelling
law dmw_saved_example:
  {dmw_saved_fits(Dm.Default{5n}) == True{} : Bool} & {FDm.put_saved(Dm.NoDefault{}, FDm.put_saved(Dm.Default{5n}, "")) == "0,1,5," : String}

# LAW dmw_next_example (R1): anchor and witness: the chain's pick is 0 (none) or 1, then it
# EXCLUDES: a vacuous dmw_next_round_trip, another spelling
law dmw_next_example:
  {dmw_next_fits(Dm.Next{9n}) == True{} : Bool} & {FDm.put_next(Dm.NoNext{}, FDm.put_next(Dm.Next{9n}, "")) == "0,1,9," : String}

# LAW dmw_in_example (R1): anchor and witness: a request is saved, cat, key, out, next
# EXCLUDES: a vacuous dmw_in_round_trip or dmw_answers, facts in another
#   order
law dmw_in_example:
  {dmw_in_fits(Dm.In{Dm.Default{5n}, True{}, True{}, False{}, Dm.Next{9n}}) == True{} : Bool} & {FDm.put_in(Dm.In{Dm.Default{5n}, True{}, True{}, False{}, Dm.Next{9n}}, "") == "1,5,TTF1,9," : String}

# LAW dmw_key_example (R1): anchor and witness: a key is the model, then the reason
# EXCLUDES: a vacuous dmw_key_round_trip, fields in another order
law dmw_key_example:
  {dmw_key_fits(Dm.K{5n, Dm.NoCredentials{}}) == True{} : Bool} & {FDm.put_key(Dm.K{5n, Dm.NoCredentials{}}, "") == "5,1," : String}

# LAW dmw_pick_example (R1): anchor and witness: a pick is 0 (the saved default) or 1, then
# the other model
# EXCLUDES: a vacuous dmw_pick_round_trip, tags swapped
law dmw_pick_example:
  {dmw_pick_fits(Dm.Other{3n}) == True{} : Bool} & {FDm.put_pick(Dm.Saved{}, FDm.put_pick(Dm.Other{3n}, "")) == "0,1,3," : String}

# LAW dmw_sub_example (R1): anchor and witness: a substitution is 0 (kept) or 1, then a key
# EXCLUDES: a vacuous dmw_sub_round_trip, tags swapped
law dmw_sub_example:
  {dmw_sub_fits(Dm.Swapped{Dm.K{5n, Dm.NotInCatalog{}}}) == True{} : Bool} & {FDm.put_sub(Dm.Kept{}, FDm.put_sub(Dm.Swapped{Dm.K{5n, Dm.NotInCatalog{}}}, "")) == "0,1,5,0," : String}

# LAW dmw_res_example (R1): anchor and witness: a reply is 0 pick sub (runs) | 1 (no model) |
# 2 key (refused)
# EXCLUDES: a vacuous dmw_res_round_trip, tags in another order
law dmw_res_example:
  {dmw_res_fits(Dm.Runs{Dm.Other{3n}, Dm.Swapped{Dm.K{5n, Dm.NotInScope{}}}}) == True{} : Bool} & {FDm.put_res(Dm.Runs{Dm.Other{3n}, Dm.Swapped{Dm.K{5n, Dm.NotInScope{}}}}, FDm.put_res(Dm.Nothing{}, FDm.put_res(Dm.Refused{Dm.K{5n, Dm.NoCredentials{}}}, ""))) == "0,1,3,1,5,2,1,2,5,1," : String}

# LAW dmw_ffi_example (R2): anchor: a usable saved default runs, end to end
# EXCLUDES: an entry that answers other bytes than the grammar's
law dmw_ffi_example:
  {FDm.ffi("1,5,TTF1,9,") == "0,0,0," : String}

# LAW dmw_malformed_example (R3): anchor: a saved default with an unknown tag (2) answers
# the malformed error
# EXCLUDES: an unknown saved tag read as a request
law dmw_malformed_example:
  {FDm.ffi("2,") == Wr.err("default_model: malformed request") : String}

# The default_model entry, spelled by the grammar Rust writes and reads
# (crates/eukhe-core/src/models/resolver.rs `resolve_default`), not by the
# entry's own encoders

# a saved default: 0 (none) | 1, then the model
def dmw_spell_saved(x: Dm.Saved, rest: String) -> String:
  match x:
    case Dm.NoDefault{}:
      Wr.put_nat(0n, rest)
    case Dm.Default{m}:
      Wr.put_nat(1n, Wr.put_nat(m, rest))

# the chain's pick: 0 (none) | 1, then the model
def dmw_spell_next(x: Dm.Next, rest: String) -> String:
  match x:
    case Dm.NoNext{}:
      Wr.put_nat(0n, rest)
    case Dm.Next{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

# a request: the saved default, then catalog, credentials, out of scope
# (T or F each), then the chain's pick, then rest
def dmw_spell_req(x: Dm.In, rest: String) -> String:
  match x:
    case Dm.In{saved, cat, key, out, next}:
      dmw_spell_saved(saved, Wr.put_bool(cat, Wr.put_bool(key, Wr.put_bool(out, dmw_spell_next(next, rest)))))

# a reason: 0 not in the catalog | 1 no credentials | 2 not in the scope
def dmw_spell_reason(r: Dm.Reason, rest: String) -> String:
  match r:
    case Dm.NotInCatalog{}:
      Wr.put_nat(0n, rest)
    case Dm.NoCredentials{}:
      Wr.put_nat(1n, rest)
    case Dm.NotInScope{}:
      Wr.put_nat(2n, rest)

# a key: the model, then the reason
def dmw_spell_key(k: Dm.Key, rest: String) -> String:
  match k:
    case Dm.K{m, r}:
      Wr.put_nat(m, dmw_spell_reason(r, rest))

# a pick: 0 (the saved default) | 1, then the other model
def dmw_spell_pick(p: Dm.Pick, rest: String) -> String:
  match p:
    case Dm.Saved{}:
      Wr.put_nat(0n, rest)
    case Dm.Other{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

# a substitution: 0 (kept) | 1, then the key
def dmw_spell_sub(s: Dm.Sub, rest: String) -> String:
  match s:
    case Dm.Kept{}:
      Wr.put_nat(0n, rest)
    case Dm.Swapped{k}:
      Wr.put_nat(1n, dmw_spell_key(k, rest))

# a reply: 0, pick, sub (runs) | 1 (no model) | 2, key (refused)
def dmw_spell_res(r: Dm.Res, rest: String) -> String:
  match r:
    case Dm.Runs{p, s}:
      Wr.put_nat(0n, dmw_spell_pick(p, dmw_spell_sub(s, rest)))
    case Dm.Nothing{}:
      Wr.put_nat(1n, rest)
    case Dm.Refused{k}:
      Wr.put_nat(2n, dmw_spell_key(k, rest))

# the spelled reply of the resolver's answer (pinned case by case by the
# default_* laws) on request x
def dmw_spell_answer(x: Dm.In) -> String:
  dmw_spell_res(Dm.resolve(x), "")

# LAW dmw_ffi_answers_spelled: a request spelled by the grammar, every number within the wire,
# is answered with the grammar's spelling of the resolver's answer
# EXCLUDES: a tag (saved, pick, reason, sub, reply) that drifts from the
#   grammar Rust reads and writes (swapped on both sides of the entry
#   alike), a fact (catalog, credentials, scope) read reversed or swapped,
#   a field lost, swapped or defaulted
law dmw_ffi_answers_spelled:
  for +x: Dm.In
  for fits: {dmw_in_fits(x) == True{} : Bool}
  {FDm.ffi(dmw_spell_req(x, "")) == dmw_spell_answer(x) : String}

# LAW dmw_ffi_left_over_spelled: a spelled request that fits, followed by any more input,
# answers the error form "default_model: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request, or
#   answered with another error text
law dmw_ffi_left_over_spelled:
  for +x: Dm.In
  for fits: {dmw_in_fits(x) == True{} : Bool}
  for +c: Char
  for +t: String
  {FDm.ffi(dmw_spell_req(x, SCon{c, t})) == Wr.err("default_model: input left over") : String}

# LAW dmw_ffi_unknown_saved: a saved-default tag of 2 or more (of any length) answers the error
# form "default_model: malformed request", whatever follows
# EXCLUDES: an unknown saved tag read as none or as a saved default
law dmw_ffi_unknown_saved:
  for +n: Nat
  for +rest: String
  {FDm.ffi(Wr.put_nat(2n+n, rest)) == Wr.err("default_model: malformed request") : String}

# LAW dmw_ffi_unknown_next: a spelled saved default that fits and the three facts, then a pick
# tag of 2 or more (of any length), answer the error form "default_model:
# malformed request", whatever follows
# EXCLUDES: an unknown pick tag read as none or as a model
law dmw_ffi_unknown_next:
  for +sv: Dm.Saved
  for fits: {dmw_saved_fits(sv) == True{} : Bool}
  for +cat: Bool
  for +key: Bool
  for +out: Bool
  for +n: Nat
  for +rest: String
  {FDm.ffi(dmw_spell_saved(sv, Wr.put_bool(cat, Wr.put_bool(key, Wr.put_bool(out, Wr.put_nat(2n+n, rest)))))) == Wr.err("default_model: malformed request") : String}

# LAW dmw_ffi_reads_only_requests: an answer that is not the error form answers a request: the
# input is exactly the spelling of a request whose numbers fit the wire,
# and the answer is the spelled reply of the resolver's answer on it
# EXCLUDES: a decoder that accepts an unknown tag (saved or pick), a fact
#   other than T or F, a missing or extra field, or input left over, and
#   answers it anyway (a default instead of the error form)
law dmw_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FDm.ffi(s)) == False{} : Bool}
  exs x: Dm.In
  {(s, (dmw_in_fits(x), FDm.ffi(s))) == (dmw_spell_req(x, ""), (True{}, dmw_spell_answer(x))) : String & (Bool & String)}

# LAW dmw_ffi_malformed_unless_request: every answer but the error form "default_model:
# malformed request" comes from an input that begins with a spelled request
# that fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law dmw_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FDm.ffi(s), Wr.err("default_model: malformed request")) == False{} : Bool}
  exs x: Dm.In
  exs rest: String
  {(s, dmw_in_fits(x)) == (dmw_spell_req(x, rest), True{}) : String & Bool}

# LAW dmw_ffi_tags_example: anchor: the bytes Rust sends (saved default 0, chain's pick 1)
# and reads: a usable default runs (0,0,0,) with or without a pick; nothing
# saved runs the pick (0,1,1,0,) or nothing (1,); not in the catalog swaps
# (0,1,1,1,0,0,) or refuses (2,0,0,); no credentials refuses (2,0,1,); not
# in the scope swaps (0,1,1,1,0,2,) or refuses (2,0,2,); a saved tag 2, a
# pick tag 2, a fact X and no input are malformed; a request with input
# left over is refused
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, a reversed fact, an unknown tag read as a known one
law dmw_ffi_tags_example:
  {[FDm.ffi("1,0,TTF1,1,"), FDm.ffi("1,0,TTF0,"), FDm.ffi("0,FFF1,1,"), FDm.ffi("0,FFF0,"), FDm.ffi("1,0,FTF1,1,"), FDm.ffi("1,0,FFF0,"), FDm.ffi("1,0,TFF1,1,"), FDm.ffi("1,0,TTT1,1,"), FDm.ffi("1,0,TTT0,"), FDm.ffi("2,"), FDm.ffi("1,0,TTF2,"), FDm.ffi("1,0,TXF1,1,"), FDm.ffi(""), FDm.ffi("1,0,TTF1,1,x")] == ["0,0,0,", "0,0,0,", "0,1,1,0,", "1,", "0,1,1,1,0,0,", "2,0,0,", "2,0,1,", "0,1,1,1,0,2,", "2,0,2,", Wr.err("default_model: malformed request"), Wr.err("default_model: malformed request"), Wr.err("default_model: malformed request"), Wr.err("default_model: malformed request"), Wr.err("default_model: input left over")] : List<&2, String>}
