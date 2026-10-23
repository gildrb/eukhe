# eukhe: the laws of area catalog_union

import Base
import ../bend/catalog_union.bend as CU
import ../bend/ffi_catalog_union.bend as FCu
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- catalog_union ----

# LAWS (C1): the built-in model catalog is one list, the union of the
# bundled snapshot and the compiled catalog. No source hides a model the
# other has; a model in both takes each field from one stated source; the
# result does not depend on the order the sources are read. Each law is
# an open claim about the model in bend/catalog_union.bend; PROOF.bend
# proves them (as Laws.<law>) with the lemmas of
# PROOF.bend section catalog_union.

# (C1) The catalog union
# ----------------------
# crates/eukhe-models/src/effective.rs `effective_catalog`, served by
# chain.rs `ModelCatalog::models`. bs is the bundled snapshot (pinned),
# cs the compiled catalog, k a model's key (its provider and id). Every
# input is free: any entries, any order.

# LAW: no source hides a model: the built-in catalog has a model exactly
# when the bundle or the compiled catalog has it
law union_hides_nothing:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  {CU.has(CU.union(bs, cs), k) == Bool.or(CU.has(bs, k), CU.has(cs, k)) : Bool}

# LAW: one model list: when each source lists a model at most once, so
# does the built-in catalog
law union_lists_each_model_once:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for ub: {Nat.is_le(CU.count(bs, k), 1n) == True{} : Bool}
  for uc: {Nat.is_le(CU.count(cs, k), 1n) == True{} : Bool}
  {Nat.is_le(CU.count(CU.union(bs, cs), k), 1n) == True{} : Bool}

# LAW: a model that only the bundle has is the bundled entry
law union_bundled_only:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +b: CU.Ent
  for hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == None{} : Maybe<&2, CU.Ent>}
  {CU.find(CU.union(bs, cs), k) == Some{b} : Maybe<&2, CU.Ent>}

# LAW: a model that only the compiled catalog has is the compiled entry
law union_compiled_only:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +c: CU.Ent
  for hb: {CU.find(bs, k) == None{} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}
  {CU.find(CU.union(bs, cs), k) == Some{c} : Maybe<&2, CU.Ent>}

# LAW: a model in both sources takes its api and its data from the
# bundled entry, and each optional field too when the bundled entry
# states it (every field f of the four: the slot of f pins the key, api,
# data and that field)
law union_both_keeps_bundled:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +b: CU.Ent
  for +c: CU.Ent
  for +f: CU.Fld
  for +v: Nat
  for hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}
  for hv: {CU.Ent.opt(b, f) == Some{v} : Maybe<&2, Nat>}
  {CU.slot(CU.find(CU.union(bs, cs), k), f) == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), Some{v}}} : Maybe<&2, CU.Slot>}

# LAW: an optional field that the bundled entry leaves out comes from the
# compiled entry when both use the same api
law union_both_fills_from_compiled:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +b: CU.Ent
  for +c: CU.Ent
  for +f: CU.Fld
  for hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}
  for hn: {CU.Ent.opt(b, f) == None{} : Maybe<&2, Nat>}
  for ha: {Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)) == True{} : Bool}
  {CU.slot(CU.find(CU.union(bs, cs), k), f) == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), CU.Ent.opt(c, f)}} : Maybe<&2, CU.Slot>}

# LAW: and stays out when they use different apis
law union_both_other_api:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +b: CU.Ent
  for +c: CU.Ent
  for +f: CU.Fld
  for hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}
  for hn: {CU.Ent.opt(b, f) == None{} : Maybe<&2, Nat>}
  for ha: {Nat.is_eq(CU.Ent.api(b), CU.Ent.api(c)) == False{} : Bool}
  {CU.slot(CU.find(CU.union(bs, cs), k), f) == Some{CU.Slot{CU.Ent.key(b), CU.Ent.api(b), CU.Ent.data(b), None{}}} : Maybe<&2, CU.Slot>}

# LAW: the four optional fields are four: thinkingLevelMap, compat,
# featured and headers each read their own place of an entry
# EXCLUDES: a field view that reads one field for two (then the laws
#   above would leave a field free)
law union_fields_example:
  {[CU.Ent.opt(CU.Ent{0n, 0n, 0n, Some{1n}, Some{2n}, Some{3n}, Some{4n}}, CU.Tlm{}), CU.Ent.opt(CU.Ent{0n, 0n, 0n, Some{1n}, Some{2n}, Some{3n}, Some{4n}}, CU.Compat{}), CU.Ent.opt(CU.Ent{0n, 0n, 0n, Some{1n}, Some{2n}, Some{3n}, Some{4n}}, CU.Featured{}), CU.Ent.opt(CU.Ent{0n, 0n, 0n, Some{1n}, Some{2n}, Some{3n}, Some{4n}}, CU.Headers{})] == [Some{1n}, Some{2n}, Some{3n}, Some{4n}] : List<&2, Maybe<&2, Nat>>}

# LAW: the union the catalog runs (by tables keyed by the entries' keys,
# O(n log n)) is the union these laws read, entry for entry, in order
# EXCLUDES: a fast path that drops, reorders, duplicates or merges an
#   entry differently from the rule (a lost twin, a second twin, a missed
#   bundled key)
law union_fast:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  {CU.fast(bs, cs) == CU.union(bs, cs) : List<&2, CU.Ent>}

# LAW: the result does not depend on the order the sources are read: the
# bundle first or the compiled catalog first, each source with its
# entries in any order (any two lists that agree at k), the model with
# key k comes out the same
law union_order_free:
  for +k: Nat
  for +xs: List<&2, CU.Ent>
  for +xs2: List<&2, CU.Ent>
  for +ys: List<&2, CU.Ent>
  for +ys2: List<&2, CU.Ent>
  for sx: {CU.find(xs, k) == CU.find(xs2, k) : Maybe<&2, CU.Ent>}
  for sy: {CU.find(ys, k) == CU.find(ys2, k) : Maybe<&2, CU.Ent>}
  {CU.find(CU.read(CU.Cat{CU.Bundled{}, xs}, CU.Cat{CU.Compiled{}, ys}), k) == CU.find(CU.read(CU.Cat{CU.Compiled{}, ys2}, CU.Cat{CU.Bundled{}, xs2}), k) : Maybe<&2, CU.Ent>}

# LAW (compiled core) the catalog entry (bend/ffi_catalog_union.bend) reads back
# the two sources as Rust writes it, and leaves what follows untouched
# EXCLUDES: a request field misread, dropped, reordered or shifted; a
#   decoder that eats the input after the request
law catalog_union_ffi_request_round_trip:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +rest: String
  for h: {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(bs))), LawsBase.wire_nats_fit(FCu.ents(bs))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(cs))), LawsBase.wire_nats_fit(FCu.ents(cs)))) == True{} : Bool}
  {FCu.get_req(FCu.put_req(FCu.Req{bs, cs}, rest)) == Wr.Got{FCu.Req{bs, cs}, rest} : Wr.Dec<FCu.Req>}

# LAW (compiled core) the catalog entry answers a whole request with the
# model's union
# EXCLUDES: an entry that answers another rule, a default, or a reply for
#   a request it misread
law catalog_union_ffi_answers:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for h: {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(bs))), LawsBase.wire_nats_fit(FCu.ents(bs))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(cs))), LawsBase.wire_nats_fit(FCu.ents(cs)))) == True{} : Bool}
  {FCu.ffi(FCu.put_req(FCu.Req{bs, cs}, "")) == FCu.put_ns(FCu.ents(CU.fast(bs, cs)), "") : String}

# LAW (compiled core) the catalog entry answers a malformed request with
# the error form, never a default
# EXCLUDES: a decision made on input that is no request
law catalog_union_ffi_rejects_malformed:
  for +s: String
  for bad: {FCu.get_req(s) == Wr.Bad{} : Wr.Dec<FCu.Req>}
  {LawsBase.wire_opens_err(FCu.ffi(s)) == True{} : Bool}

# LAW (compiled core) and a request followed by more input with the error
# form
# EXCLUDES: an entry that ignores input left over (a second request, a
#   truncated one)
law catalog_union_ffi_rejects_left_over:
  for +s: String
  for +q: FCu.Req
  for +r: String
  for got: {FCu.get_req(s) == Wr.Got{q, r} : Wr.Dec<FCu.Req>}
  for more: {String.is_empty(r) == False{} : Bool}
  {LawsBase.wire_opens_err(FCu.ffi(s)) == True{} : Bool}
