# eukhe: the proof of LAW catalog_union_ffi_answers_spelled
#
# PROOF: the entry's entries are the spec's seven Nats (cua.ents, field by
# field), so the spec's spelling of a request is the entry's put_req
# (cua.req) and its fit the entry's (cua.fits); catalog_union_ffi_answers
# answers it with the fast union, which is the union (union_fast),
# spelled as the spec does (cua.reply).

import Base
import ../../bend/catalog_union.bend as CU
import ../../bend/ffi_catalog_union.bend as FCu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/catalog_union.bend as CatalogUnion
import ../../laws/wire.bend as Wire
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ./catalog_union_ffi_answers.bend as PCatalogUnionFfiAnswers
import ./union_fast.bend as PUnionFast

# the entry's optional fields and entries are the spec's
def cua.opt(m: Maybe<&2, Nat>) -> {FCu.opt(m) == CatalogUnion.cu_opt(m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def cua.ents(es: List<&2, CU.Ent>) -> {FCu.ents(es) == CatalogUnion.cu_ents(es) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case CU.Ent{k, a, d, t, c, f, h} <> rest:
      %cua.opt(t) : {FCu.ents(CU.Ent{k, a, d, t, c, f, h} <> rest) == k <> a <> d <> _ <> CatalogUnion.cu_opt(c) <> CatalogUnion.cu_opt(f) <> CatalogUnion.cu_opt(h) <> CatalogUnion.cu_ents(rest) : List<&2, Nat>}
      %cua.opt(c) : {FCu.ents(CU.Ent{k, a, d, t, c, f, h} <> rest) == k <> a <> d <> FCu.opt(t) <> _ <> CatalogUnion.cu_opt(f) <> CatalogUnion.cu_opt(h) <> CatalogUnion.cu_ents(rest) : List<&2, Nat>}
      %cua.opt(f) : {FCu.ents(CU.Ent{k, a, d, t, c, f, h} <> rest) == k <> a <> d <> FCu.opt(t) <> FCu.opt(c) <> _ <> CatalogUnion.cu_opt(h) <> CatalogUnion.cu_ents(rest) : List<&2, Nat>}
      %cua.opt(h) : {FCu.ents(CU.Ent{k, a, d, t, c, f, h} <> rest) == k <> a <> d <> FCu.opt(t) <> FCu.opt(c) <> FCu.opt(f) <> _ <> CatalogUnion.cu_ents(rest) : List<&2, Nat>}
      %cua.ents(rest) : {FCu.ents(CU.Ent{k, a, d, t, c, f, h} <> rest) == k <> a <> d <> FCu.opt(t) <> FCu.opt(c) <> FCu.opt(f) <> FCu.opt(h) <> _ : List<&2, Nat>}
      {==}

# the spec's spelling of a request is the entry's
def cua.req(+b: List<&2, CU.Ent>, +c: List<&2, CU.Ent>, +rest: String) -> {FCu.put_req(FCu.Req{b, c}, rest) == CatalogUnion.cu_spell_req(FCu.Req{b, c}, rest) : String}:
  %cua.ents(b) : {FCu.put_req(FCu.Req{b, c}, rest) == LawsBase.wire_spell_nats(_, LawsBase.wire_spell_nats(CatalogUnion.cu_ents(c), rest)) : String}
  %cua.ents(c) : {FCu.put_req(FCu.Req{b, c}, rest) == LawsBase.wire_spell_nats(FCu.ents(b), LawsBase.wire_spell_nats(_, rest)) : String}
  %Wire.wire_nats_spells(FCu.ents(c), rest) : {FCu.put_req(FCu.Req{b, c}, rest) == LawsBase.wire_spell_nats(FCu.ents(b), _) : String}
  Wire.wire_nats_spells(FCu.ents(b), FCu.put_ns(FCu.ents(c), rest))

# a request that fits as the spec says fits as the entry's laws ask
def cua.fits(+b: List<&2, CU.Ent>, +c: List<&2, CU.Ent>, fits: {CatalogUnion.cu_req_fits(FCu.Req{b, c}) == True{} : Bool}) -> {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(b))), LawsBase.wire_nats_fit(FCu.ents(b))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(c))), LawsBase.wire_nats_fit(FCu.ents(c)))) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, FCu.ents(b), CatalogUnion.cu_ents(b), cua.ents(b)) : {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, _)), LawsBase.wire_nats_fit(FCu.ents(b))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(c))), LawsBase.wire_nats_fit(FCu.ents(c)))) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, FCu.ents(b), CatalogUnion.cu_ents(b), cua.ents(b)) : {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, CatalogUnion.cu_ents(b))), LawsBase.wire_nats_fit(_)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(c))), LawsBase.wire_nats_fit(FCu.ents(c)))) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, FCu.ents(c), CatalogUnion.cu_ents(c), cua.ents(c)) : {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, CatalogUnion.cu_ents(b))), LawsBase.wire_nats_fit(CatalogUnion.cu_ents(b))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, _)), LawsBase.wire_nats_fit(FCu.ents(c)))) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, FCu.ents(c), CatalogUnion.cu_ents(c), cua.ents(c)) : {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, CatalogUnion.cu_ents(b))), LawsBase.wire_nats_fit(CatalogUnion.cu_ents(b))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, CatalogUnion.cu_ents(c))), LawsBase.wire_nats_fit(_))) == True{} : Bool}
  fits

# the entry's reply to a request read whole is the spelled union
def cua.reply(+b: List<&2, CU.Ent>, +c: List<&2, CU.Ent>) -> {FCu.put_ns(FCu.ents(CU.fast(b, c)), "") == CatalogUnion.cu_spell_answer(FCu.Req{b, c}) : String}:
  %CatalogUnion.union_fast(b, c) : {FCu.put_ns(FCu.ents(CU.fast(b, c)), "") == LawsBase.wire_spell_nats(CatalogUnion.cu_ents(_), "") : String}
  %cua.ents(CU.fast(b, c)) : {FCu.put_ns(FCu.ents(CU.fast(b, c)), "") == LawsBase.wire_spell_nats(_, "") : String}
  Wire.wire_nats_spells(FCu.ents(CU.fast(b, c)), "")

def cua.main(q: FCu.Req, fits: {CatalogUnion.cu_req_fits(q) == True{} : Bool}) -> {FCu.ffi(CatalogUnion.cu_spell_req(q, "")) == CatalogUnion.cu_spell_answer(q) : String}:
  match q:
    case FCu.Req{+b, +c}:
      %cua.req(b, c, "") : {FCu.ffi(_) == CatalogUnion.cu_spell_answer(FCu.Req{b, c}) : String}
      Equal.trans(String, FCu.ffi(FCu.put_req(FCu.Req{b, c}, "")), FCu.put_ns(FCu.ents(CU.fast(b, c)), ""), CatalogUnion.cu_spell_answer(FCu.Req{b, c}), CatalogUnion.catalog_union_ffi_answers(b, c, cua.fits(b, c, fits)), cua.reply(b, c))

def CatalogUnion.catalog_union_ffi_answers_spelled(q, fits):
  cua.main(q, fits)
