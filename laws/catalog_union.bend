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

# The entry from the requirement
# ------------------------------
# The spec of the whole entry, written from the requirement (C1: the
# union has the bundled entries in bundled order, each with its compiled
# twin, the first compiled entry with its key; then the compiled entries
# whose key the bundle lacks, in compiled order; a bundled entry with a
# twin keeps its key, api and data and each optional field it states, and
# takes each one it leaves out from the twin when both use the same api)
# and the wire's primitives only: no function of bend/catalog_union.bend
# or bend/ffi_catalog_union.bend (their types only).

# e when b holds, else r
def cu_sp_pick(b: Bool, e: CU.Ent, r: Maybe<&2, CU.Ent>) -> Maybe<&2, CU.Ent>:
  match b:
    case True{}:
      Some{e}
    case False{}:
      r

# the key of an entry
def cu_sp_key(e: CU.Ent) -> Nat:
  match e:
    case CU.Ent{k, a, d, t, c, f, h}:
      k

# the first entry of xs with key k
def cu_sp_find(xs: List<&2, CU.Ent>, +k: Nat) -> Maybe<&2, CU.Ent>:
  match xs:
    case Nil{}:
      None{}
    case +e <> rest:
      cu_sp_pick(Nat.is_eq(cu_sp_key(e), k), e, cu_sp_find(rest, k))

# an optional field: the bundled one when it states one, else the
# compiled one when both use the same api, else none
def cu_sp_fill(o: Maybe<&2, Nat>, c: Maybe<&2, Nat>, same: Bool) -> Maybe<&2, Nat>:
  match o:
    case Some{v}:
      Some{v}
    case None{}:
      match same:
        case True{}:
          c
        case False{}:
          None{}

# a bundled entry with its compiled twin
def cu_sp_merge(b: CU.Ent, c: CU.Ent) -> CU.Ent:
  match b c:
    case CU.Ent{bk, +ba, bd, bt, bc, bf, bh} CU.Ent{ck, +ca, cd, ct, cc, cf, ch}:
      +same = Nat.is_eq(ba, ca)
      CU.Ent{bk, ba, bd, cu_sp_fill(bt, ct, same), cu_sp_fill(bc, cc, same), cu_sp_fill(bf, cf, same), cu_sp_fill(bh, ch, same)}

def cu_sp_with(b: CU.Ent, m: Maybe<&2, CU.Ent>) -> CU.Ent:
  match m:
    case None{}:
      b
    case Some{c}:
      cu_sp_merge(b, c)

# every bundled entry, with its compiled twin
def cu_sp_bundled(bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> rest:
      cu_sp_with(b, cu_sp_find(cs, cu_sp_key(b))) <> cu_sp_bundled(rest, cs)

# c in front of r unless the bundle has its key (seen)
def cu_sp_keep(seen: Bool, c: CU.Ent, r: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  match seen:
    case True{}:
      r
    case False{}:
      c <> r

# the compiled entries whose key the bundle bs lacks
def cu_sp_extra(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      cu_sp_keep(Maybe.is_some(&2, CU.Ent, cu_sp_find(bs, cu_sp_key(c))), c, cu_sp_extra(rest, bs))

# the built-in catalog of the bundle bs and the compiled catalog cs
def cu_sp_union(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  List.append(&2, CU.Ent, cu_sp_bundled(bs, cs), cu_sp_extra(cs, bs))

# an optional field on the wire: 0 none, 1 + v the value v
def cu_sp_opt(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{v}:
      1n+v

def cu_sp_opt_of(n: Nat) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+v:
      Some{v}

# the entries of es, seven Nats each: key, api, data, then each optional
# field
def cu_sp_ents(es: List<&2, CU.Ent>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case CU.Ent{k, a, d, t, c, f, h} <> rest:
      k <> a <> d <> cu_sp_opt(t) <> cu_sp_opt(c) <> cu_sp_opt(f) <> cu_sp_opt(h) <> cu_sp_ents(rest)

def cu_sp_ents_of.cons(e: CU.Ent, m: Maybe<&2, List<&2, CU.Ent>>) -> Maybe<&2, List<&2, CU.Ent>>:
  match m:
    case None{}:
      None{}
    case Some{es}:
      Some{e <> es}

# the entries ns spells, seven Nats each; none when a group is short
def cu_sp_ents_of(ns: List<&2, Nat>) -> Maybe<&2, List<&2, CU.Ent>>:
  match ns:
    case Nil{}:
      Some{Nil{}}
    case k <> n1:
      match n1:
        case Nil{}:
          None{}
        case a <> n2:
          match n2:
            case Nil{}:
              None{}
            case d <> n3:
              match n3:
                case Nil{}:
                  None{}
                case t <> n4:
                  match n4:
                    case Nil{}:
                      None{}
                    case c <> n5:
                      match n5:
                        case Nil{}:
                          None{}
                        case f <> n6:
                          match n6:
                            case Nil{}:
                              None{}
                            case h <> rest:
                              cu_sp_ents_of.cons(CU.Ent{k, a, d, cu_sp_opt_of(t), cu_sp_opt_of(c), cu_sp_opt_of(f), cu_sp_opt_of(h)}, cu_sp_ents_of(rest))

def cu_sp_read.both(mb: Maybe<&2, List<&2, CU.Ent>>, mc: Maybe<&2, List<&2, CU.Ent>>, s: String) -> Wr.Dec<FCu.Req>:
  match mb:
    case None{}:
      Wr.Bad{}
    case Some{b}:
      match mc:
        case None{}:
          Wr.Bad{}
        case Some{c}:
          Wr.Got{FCu.Req{b, c}, s}

def cu_sp_read.c(b: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FCu.Req>:
  match r:
    case Wr.Got{c, s}:
      cu_sp_read.both(cu_sp_ents_of(b), cu_sp_ents_of(c), s)
    case Wr.Bad{}:
      Wr.Bad{}

def cu_sp_read.b(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FCu.Req>:
  match r:
    case Wr.Got{b, s}:
      cu_sp_read.c(b, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

# the two sources s starts with (each one list of Nats), and what follows
def cu_sp_read(s: String) -> Wr.Dec<FCu.Req>:
  cu_sp_read.b(Wr.get_list(~Nat, ~Wr.get_nat, s))

def cu_sp.end(whole: Bool, q: FCu.Req) -> String:
  match whole:
    case True{}:
      match q:
        case FCu.Req{b, c}:
          Wr.put_list(~Nat, ~Wr.put_nat, cu_sp_ents(cu_sp_union(b, c)), "")
    case False{}:
      Wr.err("catalog_union: input left over")

def cu_sp.run(r: Wr.Dec<FCu.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      cu_sp.end(Wr.end(s), q)
    case Wr.Bad{}:
      Wr.err("catalog_union: malformed request")

# the entry's answer to the input s
def cu_spec(s: String) -> String:
  cu_sp.run(cu_sp_read(s))

# LAW catalog_union_ffi_exact (compiled core): on every input the catalog entry answers the
# spec's union of the two sources the input is exactly (the bundled
# entries in order, each merged with its first compiled twin; then the
# compiled entries the bundle lacks, in order), exactly "catalog_union:
# input left over" for sources followed by more input, and exactly
# "catalog_union: malformed request" for any other input
# EXCLUDES: a model hidden, duplicated or reordered, a field taken from
#   the wrong source, a twin other than the first, an entry misread or
#   misspelled, a default for malformed input, input left over ignored,
#   another error text
law catalog_union_ffi_exact:
  for +s: String
  {FCu.ffi(s) == cu_spec(s) : String}
