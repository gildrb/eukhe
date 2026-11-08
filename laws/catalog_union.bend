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

# (C1) The union, entry by entry, against a spec
# ---------------------------------------------
# The laws above read the union through CU.find (the first entry with a
# key) and the model's own field views: the order of the list the entry
# answers, and an entry behind a duplicated key, are free in them (a
# union that lists the compiled-only models first, or reverses the
# bundle, passes them). The spec below is the union in the order the
# module docs of crates/eukhe-models/src/effective.rs state: every bundled
# entry in order, each with its compiled twin (the first compiled entry
# with its key) merged in, then every compiled entry whose key the bundle
# lacks, in order.

# the key of an entry
def cu_key(e: CU.Ent) -> Nat:
  match e:
    case CU.Ent{k, a, d, t, c, f, h}:
      k

def cu_pick(hit: Bool, e: CU.Ent, rest: Maybe<&2, CU.Ent>) -> Maybe<&2, CU.Ent>:
  match hit:
    case True{}:
      Some{e}
    case False{}:
      rest

# the first entry of xs with key k
def cu_find(xs: List<&2, CU.Ent>, +k: Nat) -> Maybe<&2, CU.Ent>:
  match xs:
    case Nil{}:
      None{}
    case +e <> rest:
      cu_pick(Nat.is_eq(cu_key(e), k), e, cu_find(rest, k))

# an optional field of a model in both: the bundled one when it states
# one, else the compiled one when both use the same api, else none
def cu_fill(o: Maybe<&2, Nat>, c: Maybe<&2, Nat>, same: Bool) -> Maybe<&2, Nat>:
  match o:
    case Some{v}:
      Some{v}
    case None{}:
      match same:
        case True{}:
          c
        case False{}:
          None{}

# the bundled entry b with its compiled twin c: key, api and data from b
def cu_merge(b: CU.Ent, c: CU.Ent) -> CU.Ent:
  match b c:
    case CU.Ent{bk, +ba, bd, bt, bc, bf, bh} CU.Ent{ck, +ca, cd, ct, cc, cf, ch}:
      +same = Nat.is_eq(ba, ca)
      CU.Ent{bk, ba, bd, cu_fill(bt, ct, same), cu_fill(bc, cc, same), cu_fill(bf, cf, same), cu_fill(bh, ch, same)}

def cu_with(+b: CU.Ent, m: Maybe<&2, CU.Ent>) -> CU.Ent:
  match m:
    case None{}:
      b
    case Some{c}:
      cu_merge(b, c)

# every bundled entry, in order, with its compiled twin merged in
def cu_bundled(bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> rest:
      cu_with(b, cu_find(cs, cu_key(b))) <> cu_bundled(rest, cs)

def cu_keep(seen: Bool, c: CU.Ent, rest: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  match seen:
    case True{}:
      rest
    case False{}:
      c <> rest

# every compiled entry whose key the bundle lacks, in order
def cu_extra(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      cu_keep(Maybe.is_some(&2, CU.Ent, cu_find(bs, cu_key(c))), c, cu_extra(rest, bs))

# the built-in catalog: the bundle merged, then the compiled-only models
def cu_union(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  List.append(&2, CU.Ent, cu_bundled(bs, cs), cu_extra(cs, bs))

# LAW union_spec: the built-in catalog is every bundled entry in order, each merged with
# its compiled twin, then every compiled entry whose key the bundle
# lacks, in order
# EXCLUDES: a union in another order (compiled-only models first, a
#   source reversed), an entry behind a duplicated key dropped, merged
#   with another twin or listed twice, a compiled entry the bundle has
#   listed again
law union_spec:
  for +bs: List<&2, CU.Ent>
  for +cs: List<&2, CU.Ent>
  {CU.union(bs, cs) == cu_union(bs, cs) : List<&2, CU.Ent>}

# LAW union_terms_exact: the model's views of an entry the laws above read (`Ent.key`,
# `Ent.api`, `Ent.data`, `Ent.opt`) are its fields
# EXCLUDES: a view that answers a constant (a mutation probe found
#   `Ent.data` free: the laws read the data through it) or another field
law union_terms_exact:
  for +k: Nat
  for +a: Nat
  for +d: Nat
  for +t: Maybe<&2, Nat>
  for +c: Maybe<&2, Nat>
  for +f: Maybe<&2, Nat>
  for +h: Maybe<&2, Nat>
  {[CU.Ent.key(CU.Ent{k, a, d, t, c, f, h}), CU.Ent.api(CU.Ent{k, a, d, t, c, f, h}), CU.Ent.data(CU.Ent{k, a, d, t, c, f, h})] == [k, a, d] : List<&2, Nat>} & {[CU.Ent.opt(CU.Ent{k, a, d, t, c, f, h}, CU.Tlm{}), CU.Ent.opt(CU.Ent{k, a, d, t, c, f, h}, CU.Compat{}), CU.Ent.opt(CU.Ent{k, a, d, t, c, f, h}, CU.Featured{}), CU.Ent.opt(CU.Ent{k, a, d, t, c, f, h}, CU.Headers{})] == [t, c, f, h] : List<&2, Maybe<&2, Nat>>}

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
