# eukhe: the laws of area default_model

import Base
import ../bend/default_model.bend as Dm
import ../bend/ffi_default_model.bend as FDm
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (H4) The saved default model
# ----------------------------
# bend/default_model.bend: the session-model resolution at open.

# LAW default_honoured_or_reported: a session started with a saved default runs on it, or its notices
# name the saved default and the reason it did not run
law default_honoured_or_reported:
  for x: Dm.In
  {Dm.reported(x, Dm.open(Dm.resolve(x))) == True{} : Bool}

# LAW default_quiet_when_honoured: a session that runs on its saved default has no notice
law default_quiet_when_honoured:
  for x: Dm.In
  for h: {Dm.on_saved(Dm.Session.run(Dm.open(Dm.resolve(x)))) == True{} : Bool}
  {Dm.none(Dm.Session.notes(Dm.open(Dm.resolve(x)))) == True{} : Bool}

# LAW default_quiet_when_unset: with no saved default the session has no notice
law default_quiet_when_unset:
  for cat: Bool
  for key: Bool
  for out: Bool
  for next: Dm.Next
  {Dm.Session.notes(Dm.open(Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, next}))) == Nil{} : List<&2, Dm.Key>}

# LAW default_unkeyed_never_moves: a saved default whose provider has no credentials opens the
# session with no model: no other provider runs in its place
law default_unkeyed_never_moves:
  for m: Nat
  for out: Bool
  for next: Dm.Next
  {Dm.Session.run(Dm.open(Dm.resolve(Dm.In{Dm.Default{m}, True{}, False{}, out, next}))) == Dm.Idle{} : Dm.Run}

# The laws below pin every answer of the resolver (Dm.resolve, the Rust
# `resolve_session_model` with no requested model), case by case: nothing
# saved; the catalog, the credentials and the scope, in this order; the
# chain's pick or none.

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

# LAW dmw_answers (R2): an encoded request answers the resolver's answer, encoded
# EXCLUDES: an entry that resolves other than Dm.resolve, or drops a fact
#   on the way in or out
law dmw_answers:
  for +x: Dm.In
  for h: {dmw_in_fits(x) == True{} : Bool}
  {FDm.ffi(FDm.put_in(x, "")) == FDm.put_res(Dm.resolve(x), "") : String}

# LAW dmw_malformed (R3): a malformed request answers the error form
# EXCLUDES: a default model for a request it cannot read
law dmw_malformed:
  for +s: String
  for h: {FDm.get_in(s) == Wr.Bad{} : Wr.Dec<Dm.In>}
  {FDm.ffi(s) == Wr.err("default_model: malformed request") : String}

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

# LAW dmw_malformed_example (R3): witness: a saved default with an unknown tag is malformed
# EXCLUDES: a vacuous dmw_malformed
law dmw_malformed_example:
  {FDm.get_in("2,") == Wr.Bad{} : Wr.Dec<Dm.In>} & {FDm.ffi("2,") == Wr.err("default_model: malformed request") : String}
