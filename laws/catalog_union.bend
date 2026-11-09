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
# proves them (as CatalogUnion.<law>) with the lemmas of
# proof/catalog_union/.

# (C1) The catalog union
# ----------------------
# crates/eukhe-models/src/effective.rs `effective_catalog`, served by
# chain.rs `ModelCatalog::models`. bs is the bundled snapshot (pinned),
# cs the compiled catalog, k a model's key (its provider and id). Every
# input is free: any entries, any order.

# LAW union_hides_nothing: no source hides a model: the built-in catalog has a model exactly
# when the bundle or the compiled catalog has it
law union_hides_nothing:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  {CU.has(CU.union(bs, cs), k) == Bool.or(CU.has(bs, k), CU.has(cs, k)) : Bool}

# LAW union_lists_each_model_once: one model list: when each source lists a model at most once, so
# does the built-in catalog
law union_lists_each_model_once:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for ub: {Nat.is_le(CU.count(bs, k), 1n) == True{} : Bool}
  for uc: {Nat.is_le(CU.count(cs, k), 1n) == True{} : Bool}
  {Nat.is_le(CU.count(CU.union(bs, cs), k), 1n) == True{} : Bool}

# LAW union_bundled_only: a model that only the bundle has is the bundled entry
law union_bundled_only:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +b: CU.Ent
  for hb: {CU.find(bs, k) == Some{b} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == None{} : Maybe<&2, CU.Ent>}
  {CU.find(CU.union(bs, cs), k) == Some{b} : Maybe<&2, CU.Ent>}

# LAW union_compiled_only: a model that only the compiled catalog has is the compiled entry
law union_compiled_only:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +c: CU.Ent
  for hb: {CU.find(bs, k) == None{} : Maybe<&2, CU.Ent>}
  for hc: {CU.find(cs, k) == Some{c} : Maybe<&2, CU.Ent>}
  {CU.find(CU.union(bs, cs), k) == Some{c} : Maybe<&2, CU.Ent>}

# LAW union_both_keeps_bundled: a model in both sources takes its api and its data from the
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

# LAW union_both_fills_from_compiled: an optional field that the bundled entry leaves out comes from the
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

# LAW union_both_other_api: and stays out when they use different apis
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

# LAW union_fields_example: the four optional fields are four: thinkingLevelMap, compat,
# featured and headers each read their own place of an entry
# EXCLUDES: a field view that reads one field for two (then the laws
#   above would leave a field free)
law union_fields_example:
  {[CU.Ent.opt(CU.Ent{0n, 0n, 0n, Some{1n}, Some{2n}, Some{3n}, Some{4n}}, CU.Tlm{}), CU.Ent.opt(CU.Ent{0n, 0n, 0n, Some{1n}, Some{2n}, Some{3n}, Some{4n}}, CU.Compat{}), CU.Ent.opt(CU.Ent{0n, 0n, 0n, Some{1n}, Some{2n}, Some{3n}, Some{4n}}, CU.Featured{}), CU.Ent.opt(CU.Ent{0n, 0n, 0n, Some{1n}, Some{2n}, Some{3n}, Some{4n}}, CU.Headers{})] == [Some{1n}, Some{2n}, Some{3n}, Some{4n}] : List<&2, Maybe<&2, Nat>>}

# LAW union_fast: the union the catalog runs (by tables keyed by the entries' keys,
# O(n log n)) is the union these laws read, entry for entry, in order
# EXCLUDES: a fast path that drops, reorders, duplicates or merges an
#   entry differently from the rule (a lost twin, a second twin, a missed
#   bundled key)
law union_fast:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  {CU.fast(bs, cs) == CU.union(bs, cs) : List<&2, CU.Ent>}

# LAW union_order_free: the result does not depend on the order the sources are read: the
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

# (C1) The union, entry by entry
# ------------------------------
# The laws above read the union through CU.find (the first entry with a
# key) and the model's own views (CU.slot through Ent.key, Ent.api,
# Ent.data): the order of the list, an entry behind a duplicated key, and
# a view both sides of a law read alike are free in them. The laws below
# read the list itself, at each place, and compare it to the sources'
# constructor fields, in the order the module docs of
# crates/eukhe-models/src/effective.rs state: the bundled entries in
# bundled order, then the compiled entries whose key the bundle lacks, in
# compiled order. The helpers read an entry by its constructor, never
# through the model's views or lookups.

# the keys of the entries, in order
def cu_keys(xs: List<&2, CU.Ent>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case CU.Ent{k, a, d, t, c, f, h} <> rest:
      k <> cu_keys(rest)

# the key, api and data of each entry, in order
def cu_kad(xs: List<&2, CU.Ent>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case CU.Ent{k, a, d, t, c, f, h} <> rest:
      k <> a <> d <> cu_kad(rest)

# k is one of ks
def cu_in(ks: List<&2, Nat>, +k: Nat) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_eq(x, k), cu_in(rest, k))

def cu_bump(hit: Bool, n: Nat) -> Nat:
  match hit:
    case True{}:
      1n+n
    case False{}:
      n

# how many times k occurs in ks
def cu_times(ks: List<&2, Nat>, +k: Nat) -> Nat:
  match ks:
    case Nil{}:
      0n
    case x <> rest:
      cu_bump(Nat.is_eq(x, k), cu_times(rest, k))

def cu_sel(keep: Bool, x: CU.Ent, rest: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  match keep:
    case True{}:
      x <> rest
    case False{}:
      rest

# the entries of xs the mask m marks True, in order (an entry past the
# end of m is left out): any ordered subsequence of xs is one
def cu_select(m: List<&2, Bool>, xs: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  match m:
    case Nil{}:
      Nil{}
    case keep <> mr:
      match xs:
        case Nil{}:
          Nil{}
        case x <> rest:
          cu_sel(keep, x, cu_select(mr, rest))

# LAW union_nil_compiled: with an empty compiled catalog the built-in catalog is the
# bundle, entry for entry
# EXCLUDES: a bundled entry dropped, reordered, listed twice or changed
#   when nothing merges into it
law union_nil_compiled:
  for +bs: List<&2, CU.Ent>
  {CU.union(bs, Nil{}) == bs : List<&2, CU.Ent>}

# LAW union_nil_bundled: with an empty bundle the built-in catalog is the compiled catalog,
# entry for entry
# EXCLUDES: a compiled entry dropped, reordered, listed twice or changed
#   when the bundle is empty
law union_nil_bundled:
  for +cs: List<&2, CU.Ent>
  {CU.union(Nil{}, cs) == cs : List<&2, CU.Ent>}

# LAW union_head_is_bundle: the first entries of the built-in catalog, as many as the bundle
# has, are the bundled entries in bundled order, each with its own key,
# api and data
# EXCLUDES: compiled-only models listed first or among the bundled ones,
#   the bundle reordered, a bundled entry dropped or listed twice, a key,
#   api or data taken from the compiled twin
law union_head_is_bundle:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  {cu_kad(List.take(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs))) == cu_kad(bs) : List<&2, Nat>}

# LAW union_tail_in_compiled_order: the entries after the bundled ones are compiled entries,
# unchanged, in compiled order (an ordered subsequence of the compiled
# catalog)
# EXCLUDES: a compiled-only model changed, invented, listed twice or out of
#   compiled order, a bundled entry listed again after the bundle
law union_tail_in_compiled_order:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  exs m: List<&2, Bool>
  {cu_select(m, cs) == List.drop(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs)) : List<&2, CU.Ent>}

# LAW union_tail_lacks_bundled: no entry after the bundled ones has a key the bundle has
# EXCLUDES: a compiled twin listed again after its bundled entry (a
#   model listed twice), a twin found by another key test
law union_tail_lacks_bundled:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for hb: {cu_in(cu_keys(bs), k) == True{} : Bool}
  {cu_times(cu_keys(List.drop(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs))), k) == 0n : Nat}

# LAW union_tail_keeps_compiled_only: a key the bundle lacks occurs after the bundled entries as
# often as in the compiled catalog (with union_tail_in_compiled_order and
# union_tail_lacks_bundled: the entries after the bundled ones are exactly
# the compiled entries whose key the bundle lacks, in compiled order)
# EXCLUDES: a compiled-only model dropped or listed once of the times the
#   compiled catalog lists it
law union_tail_keeps_compiled_only:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for hb: {cu_in(cu_keys(bs), k) == False{} : Bool}
  {cu_times(cu_keys(List.drop(&2, CU.Ent, CU.union(bs, cs), List.length(&2, CU.Ent, bs))), k) == cu_times(cu_keys(cs), k) : Nat}

# LAW union_at_bundled_alone: a bundled entry whose key the compiled catalog lacks is, at its
# own place in the built-in catalog (its place in the bundle), the
# bundled entry itself, every field (bundled entries before it with the
# same key or not)
# EXCLUDES: a bundled entry changed when it has no twin, an entry behind a
#   duplicated bundled key dropped or replaced by the first
law union_at_bundled_alone:
  for +bp: List<&2, CU.Ent>
  for +bq: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +k: Nat
  for +a: Nat
  for +d: Nat
  for +t: Maybe<&2, Nat>
  for +cm: Maybe<&2, Nat>
  for +ft: Maybe<&2, Nat>
  for +hd: Maybe<&2, Nat>
  for hc: {cu_in(cu_keys(cs), k) == False{} : Bool}
  {List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), cs), List.length(&2, CU.Ent, bp)) == Some{CU.Ent{k, a, d, t, cm, ft, hd}} : Maybe<&2, CU.Ent>}

# LAW union_at_both_same_api: a bundled entry whose key the compiled catalog has (its twin:
# the first compiled entry with that key) and whose twin uses the same
# api is, at its own place in the built-in catalog, the entry with the
# bundled key, api and data and, for each of the four optional fields,
# the bundled entry's when it states it, else the twin's (Maybe.or: the
# first that is Some), read by its constructor (bundled entries before
# it with the same key or not)
# EXCLUDES: a field the bundle leaves out kept out (for some keys,
#   fields, apis or values) or taken from another twin or another field;
#   a stated field replaced by the twin's; key, api or data from the
#   twin; a twin other than the first; an entry behind a duplicated
#   bundled key left unmerged
law union_at_both_same_api:
  for +bp: List<&2, CU.Ent>
  for +bq: List<&2, CU.Ent>
  for +cp: List<&2, CU.Ent>
  for +cq: List<&2, CU.Ent>
  for +k: Nat
  for +a: Nat
  for +d: Nat
  for +t: Maybe<&2, Nat>
  for +cm: Maybe<&2, Nat>
  for +ft: Maybe<&2, Nat>
  for +hd: Maybe<&2, Nat>
  for +cd: Nat
  for +ct: Maybe<&2, Nat>
  for +cc: Maybe<&2, Nat>
  for +cf: Maybe<&2, Nat>
  for +ch: Maybe<&2, Nat>
  for hp: {cu_in(cu_keys(cp), k) == False{} : Bool}
  {List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), List.append(&2, CU.Ent, cp, CU.Ent{k, a, cd, ct, cc, cf, ch} <> cq)), List.length(&2, CU.Ent, bp)) == Some{CU.Ent{k, a, d, Maybe.or(&2, Nat, t, ct), Maybe.or(&2, Nat, cm, cc), Maybe.or(&2, Nat, ft, cf), Maybe.or(&2, Nat, hd, ch)}} : Maybe<&2, CU.Ent>}

# LAW union_at_both_apis_differ: and when its twin uses another api it is, at its own place,
# the bundled entry itself, every field (a field the bundle leaves out
# stays out), read by its constructor
# EXCLUDES: a field filled from a twin of another api; a stated field,
#   key, api or data from the twin
law union_at_both_apis_differ:
  for +bp: List<&2, CU.Ent>
  for +bq: List<&2, CU.Ent>
  for +cp: List<&2, CU.Ent>
  for +cq: List<&2, CU.Ent>
  for +k: Nat
  for +a: Nat
  for +d: Nat
  for +t: Maybe<&2, Nat>
  for +cm: Maybe<&2, Nat>
  for +ft: Maybe<&2, Nat>
  for +hd: Maybe<&2, Nat>
  for +ca: Nat
  for +cd: Nat
  for +ct: Maybe<&2, Nat>
  for +cc: Maybe<&2, Nat>
  for +cf: Maybe<&2, Nat>
  for +ch: Maybe<&2, Nat>
  for hp: {cu_in(cu_keys(cp), k) == False{} : Bool}
  for ha: {Nat.is_eq(a, ca) == False{} : Bool}
  {List.get(&2, CU.Ent, CU.union(List.append(&2, CU.Ent, bp, CU.Ent{k, a, d, t, cm, ft, hd} <> bq), List.append(&2, CU.Ent, cp, CU.Ent{k, ca, cd, ct, cc, cf, ch} <> cq)), List.length(&2, CU.Ent, bp)) == Some{CU.Ent{k, a, d, t, cm, ft, hd}} : Maybe<&2, CU.Ent>}

# LAW catalog_union_ffi_request_round_trip (compiled core): the catalog entry (bend/ffi_catalog_union.bend) reads back
# the two sources as Rust writes it, and leaves what follows untouched
# EXCLUDES: a request field misread, dropped, reordered or shifted; a
#   decoder that eats the input after the request
law catalog_union_ffi_request_round_trip:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for +rest: String
  for h: {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(bs))), LawsBase.wire_nats_fit(FCu.ents(bs))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(cs))), LawsBase.wire_nats_fit(FCu.ents(cs)))) == True{} : Bool}
  {FCu.get_req(FCu.put_req(FCu.Req{bs, cs}, rest)) == Wr.Got{FCu.Req{bs, cs}, rest} : Wr.Dec<FCu.Req>}

# LAW catalog_union_ffi_answers (compiled core): the catalog entry answers a whole request with the
# model's union
# EXCLUDES: an entry that answers another rule, a default, or a reply for
#   a request it misread
law catalog_union_ffi_answers:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  for h: {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(bs))), LawsBase.wire_nats_fit(FCu.ents(bs))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(cs))), LawsBase.wire_nats_fit(FCu.ents(cs)))) == True{} : Bool}
  {FCu.ffi(FCu.put_req(FCu.Req{bs, cs}, "")) == FCu.put_ns(FCu.ents(CU.fast(bs, cs)), "") : String}

# LAW catalog_union_ffi_rejects_malformed (compiled core): the catalog entry answers a malformed request with
# the error form, never a default
# EXCLUDES: a decision made on input that is no request
law catalog_union_ffi_rejects_malformed:
  for +s: String
  for bad: {FCu.get_req(s) == Wr.Bad{} : Wr.Dec<FCu.Req>}
  {LawsBase.wire_opens_err(FCu.ffi(s)) == True{} : Bool}

# LAW catalog_union_ffi_rejects_left_over (compiled core): and a request followed by more input with the error
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

# (C1) The catalog entry, spelled
# -------------------------------
# The entry laws above read and write through the entry's own encoders
# (FCu.put_req, FCu.ents, FCu.put_ns): a drift both sides share (two
# fields swapped, an optional field's offset, the two sources read in the
# other order) passes them. The laws below spell the request and the
# reply with the wire primitives as Rust writes and reads them
# (crates/eukhe-models/src/effective.rs `union`): the bundle, then the
# compiled catalog, each a wire list of Nats with seven per entry (key,
# api, data, then thinkingLevelMap, compat, featured and headers: 0 none,
# 1 + v the place v); the reply is the union, seven Nats per entry.

# an optional field as Rust writes it: 0 none, 1 + v the place v
def cu_opt(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{v}:
      1n+v

# the entries, seven Nats each, in order
def cu_ents(es: List<&2, CU.Ent>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case CU.Ent{k, a, d, t, c, f, h} <> rest:
      k <> a <> d <> cu_opt(t) <> cu_opt(c) <> cu_opt(f) <> cu_opt(h) <> cu_ents(rest)

# a request as Rust spells it: the bundle, the compiled catalog, then rest
def cu_spell_req(q: FCu.Req, rest: String) -> String:
  match q:
    case FCu.Req{b, c}:
      LawsBase.wire_spell_nats(cu_ents(b), LawsBase.wire_spell_nats(cu_ents(c), rest))

# every count and Nat of a request fits the wire
def cu_req_fits(q: FCu.Req) -> Bool:
  match q:
    case FCu.Req{b, c}:
      +eb = cu_ents(b)
      +ec = cu_ents(c)
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, eb)), LawsBase.wire_nats_fit(eb)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ec)), LawsBase.wire_nats_fit(ec)))

# the spelled reply to a request: the union the laws above read
# (union_fast pins the entry's fast union to it)
def cu_spell_answer(q: FCu.Req) -> String:
  match q:
    case FCu.Req{+b, +c}:
      LawsBase.wire_spell_nats(cu_ents(CU.union(b, c)), "")

# LAW catalog_union_ffi_answers_spelled: a request spelled as Rust writes it, every count and
# Nat within the wire, is answered with the union, seven Nats per entry
# as Rust reads them
# EXCLUDES: a request or reply drift both sides of the Bend entry share
#   (fields swapped, an optional field read as none or offset, the
#   sources read in the other order), an answer other than the union
law catalog_union_ffi_answers_spelled:
  for +q: FCu.Req
  for fits: {cu_req_fits(q) == True{} : Bool}
  {FCu.ffi(cu_spell_req(q, "")) == cu_spell_answer(q) : String}

# LAW catalog_union_ffi_left_over_spelled: a spelled request that fits, followed by any more input,
# answers the error form "catalog_union: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request, or
#   answered with another error text
law catalog_union_ffi_left_over_spelled:
  for +q: FCu.Req
  for fits: {cu_req_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FCu.ffi(cu_spell_req(q, SCon{c, t})) == Wr.err("catalog_union: input left over") : String}

# LAW catalog_union_ffi_reads_only_requests: an answer that is not the error form answers a
# request: the input is exactly the spelling of a request whose counts and
# Nats fit the wire, and the answer is the spelled union
# EXCLUDES: a decoder that accepts a list whose length is not a multiple
#   of seven, a missing list, a short list or input left over, and answers
#   it anyway (a default instead of the error form)
law catalog_union_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCu.ffi(s)) == False{} : Bool}
  exs q: FCu.Req
  {(s, (cu_req_fits(q), FCu.ffi(s))) == (cu_spell_req(q, ""), (True{}, cu_spell_answer(q))) : String & (Bool & String)}

# LAW catalog_union_ffi_malformed_unless_request: every answer but the error form "catalog_union:
# malformed request" comes from an input that begins with a spelled
# request that fits (with catalog_union_ffi_answers_spelled and
# catalog_union_ffi_left_over_spelled this pins the entry's answer to
# every input)
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law catalog_union_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FCu.ffi(s), Wr.err("catalog_union: malformed request")) == False{} : Bool}
  exs q: FCu.Req
  exs rest: String
  {(s, cu_req_fits(q)) == (cu_spell_req(q, rest), True{}) : String & Bool}

# LAW catalog_union_ffi_tags_example: anchor: the bytes Rust sends and reads: a bundled entry
# with its thinkingLevelMap at place 0 alone (1 for the field); a model in
# both with the same api takes the compiled thinkingLevelMap (place 1, so
# 2) and with another api none; a compiled-only model; a bundled and a
# compiled model, the bundled first; a bundle of six Nats, a compiled list
# short of its count and a missing compiled list are malformed; input
# after the request is left over
# EXCLUDES: a field order or optional-field offset both sides of the Bend
#   entry agree on but Rust does not, the sources read in the other order
law catalog_union_ffi_tags_example:
  {[FCu.ffi("7,0,0,0,1,0,0,0,0,"), FCu.ffi("7,0,0,0,0,0,0,0,7,0,0,1,2,0,0,0,"), FCu.ffi("7,0,0,0,0,0,0,0,7,0,1,1,2,0,0,0,"), FCu.ffi("0,7,1,0,0,0,1,0,0,"), FCu.ffi("7,0,0,0,0,0,0,0,7,1,0,1,0,0,0,0,"), FCu.ffi("6,0,0,0,0,0,0,0,"), FCu.ffi("0,1,0,"), FCu.ffi("0,"), FCu.ffi("0,0,x")] == ["7,0,0,0,1,0,0,0,", "7,0,0,0,2,0,0,0,", "7,0,0,0,0,0,0,0,", "7,1,0,0,0,1,0,0,", "14,0,0,0,0,0,0,0,1,0,1,0,0,0,0,", Wr.err("catalog_union: malformed request"), Wr.err("catalog_union: malformed request"), Wr.err("catalog_union: malformed request"), Wr.err("catalog_union: input left over")] : List<&2, String>}
