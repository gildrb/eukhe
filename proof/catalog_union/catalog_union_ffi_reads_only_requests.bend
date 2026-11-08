# eukhe: the proof of LAW catalog_union_ffi_reads_only_requests
#
# PROOF: each list the decoder reads is spelled and fits (NL.nl.nl); the
# entries FCu.ents.of reads from a list are seven Nats each, and the spec
# spells them back to that list (cro.eo, each optional field's Nat read
# back by cro.opt_back); so the request read is spelled and fits
# (cro.req); the answer is the error form unless the request was read
# whole, nothing left, and then it is the spelled union (cro.fin with
# cua.reply).

import Base
import ../../bend/catalog_union.bend as CU
import ../../bend/ffi_catalog_union.bend as FCu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/catalog_union.bend as CatalogUnion
import ../wire/base/spell.bend as LAWireSpell
import ../tools/tools_ffi_reads_only_requests/nats.bend as NL
import ./catalog_union_ffi_answers_spelled.bend as PCatalogUnionFfiAnswersSpelled

# Entries read
# ------------

# an optional field's Nat read and spelled again is the Nat
def cro.opt_back(n: Nat) -> {CatalogUnion.cu_opt(FCu.opt.of(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+v:
      {==}

# the entries read from ns spell ns
def cro.EO(ns: List<&2, Nat>, m: Maybe<&2, List<&2, CU.Ent>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{es}:
      {ns == CatalogUnion.cu_ents(es) : List<&2, Nat>}

def cro.cons(+k: Nat, +a: Nat, +d: Nat, +t: Nat, +c: Nat, +f: Nat, +h: Nat, +rest: List<&2, Nat>, m: Maybe<&2, List<&2, CU.Ent>>, ih: cro.EO(rest, m)) -> cro.EO(k <> a <> d <> t <> c <> f <> h <> rest, FCu.ents.cons(CU.Ent{k, a, d, FCu.opt.of(t), FCu.opt.of(c), FCu.opt.of(f), FCu.opt.of(h)}, m)):
  match m:
    case None{}:
      Unit{}
    case Some{es}:
      %Equal.sym(Nat, CatalogUnion.cu_opt(FCu.opt.of(t)), t, cro.opt_back(t)) : {k <> a <> d <> t <> c <> f <> h <> rest == k <> a <> d <> _ <> CatalogUnion.cu_opt(FCu.opt.of(c)) <> CatalogUnion.cu_opt(FCu.opt.of(f)) <> CatalogUnion.cu_opt(FCu.opt.of(h)) <> CatalogUnion.cu_ents(es) : List<&2, Nat>}
      %Equal.sym(Nat, CatalogUnion.cu_opt(FCu.opt.of(c)), c, cro.opt_back(c)) : {k <> a <> d <> t <> c <> f <> h <> rest == k <> a <> d <> t <> _ <> CatalogUnion.cu_opt(FCu.opt.of(f)) <> CatalogUnion.cu_opt(FCu.opt.of(h)) <> CatalogUnion.cu_ents(es) : List<&2, Nat>}
      %Equal.sym(Nat, CatalogUnion.cu_opt(FCu.opt.of(f)), f, cro.opt_back(f)) : {k <> a <> d <> t <> c <> f <> h <> rest == k <> a <> d <> t <> c <> _ <> CatalogUnion.cu_opt(FCu.opt.of(h)) <> CatalogUnion.cu_ents(es) : List<&2, Nat>}
      %Equal.sym(Nat, CatalogUnion.cu_opt(FCu.opt.of(h)), h, cro.opt_back(h)) : {k <> a <> d <> t <> c <> f <> h <> rest == k <> a <> d <> t <> c <> f <> _ <> CatalogUnion.cu_ents(es) : List<&2, Nat>}
      %ih : {k <> a <> d <> t <> c <> f <> h <> rest == k <> a <> d <> t <> c <> f <> h <> _ : List<&2, Nat>}
      {==}

def cro.eo(ns: List<&2, Nat>) -> cro.EO(ns, FCu.ents.of(ns)):
  match ns:
    case Nil{}:
      {==}
    case k <> n1:
      match n1:
        case Nil{}:
          Unit{}
        case a <> n2:
          match n2:
            case Nil{}:
              Unit{}
            case d <> n3:
              match n3:
                case Nil{}:
                  Unit{}
                case t <> n4:
                  match n4:
                    case Nil{}:
                      Unit{}
                    case c <> n5:
                      match n5:
                        case Nil{}:
                          Unit{}
                        case f <> n6:
                          match n6:
                            case Nil{}:
                              Unit{}
                            case h <> +rest:
                              cro.cons(k, a, d, t, c, f, h, rest, FCu.ents.of(rest), cro.eo(rest))

# The decoder
# -----------

# what the decoder reads is its spelling, then its rest, and fits
def cro.Req(s: String, d: Wr.Dec<FCu.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == CatalogUnion.cu_spell_req(q, r) : String} & {CatalogUnion.cu_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cro.spell(-s: String, -bn: List<&2, Nat>, -cn: List<&2, Nat>, -s2: String, -b: List<&2, CU.Ent>, -c: List<&2, CU.Ent>, pre: {s == LawsBase.wire_spell_nats(bn, LawsBase.wire_spell_nats(cn, s2)) : String}, eb: {bn == CatalogUnion.cu_ents(b) : List<&2, Nat>}, ec: {cn == CatalogUnion.cu_ents(c) : List<&2, Nat>}) -> {s == CatalogUnion.cu_spell_req(FCu.Req{b, c}, s2) : String}:
  %eb : {s == LawsBase.wire_spell_nats(_, LawsBase.wire_spell_nats(CatalogUnion.cu_ents(c), s2)) : String}
  %ec : {s == LawsBase.wire_spell_nats(bn, LawsBase.wire_spell_nats(_, s2)) : String}
  pre

def cro.fit(-bn: List<&2, Nat>, -cn: List<&2, Nat>, -b: List<&2, CU.Ent>, -c: List<&2, CU.Ent>, fb: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, bn)), LawsBase.wire_nats_fit(bn)) == True{} : Bool}, fc: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cn)), LawsBase.wire_nats_fit(cn)) == True{} : Bool}, +eb: {bn == CatalogUnion.cu_ents(b) : List<&2, Nat>}, +ec: {cn == CatalogUnion.cu_ents(c) : List<&2, Nat>}) -> {CatalogUnion.cu_req_fits(FCu.Req{b, c}) == True{} : Bool}:
  %eb : {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, _)), LawsBase.wire_nats_fit(CatalogUnion.cu_ents(b))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, CatalogUnion.cu_ents(c))), LawsBase.wire_nats_fit(CatalogUnion.cu_ents(c)))) == True{} : Bool}
  %eb : {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, bn)), LawsBase.wire_nats_fit(_)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, CatalogUnion.cu_ents(c))), LawsBase.wire_nats_fit(CatalogUnion.cu_ents(c)))) == True{} : Bool}
  %ec : {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, bn)), LawsBase.wire_nats_fit(bn)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, _)), LawsBase.wire_nats_fit(CatalogUnion.cu_ents(c)))) == True{} : Bool}
  %ec : {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, bn)), LawsBase.wire_nats_fit(bn)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cn)), LawsBase.wire_nats_fit(_))) == True{} : Bool}
  LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, bn)), LawsBase.wire_nats_fit(bn)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cn)), LawsBase.wire_nats_fit(cn)), fb, fc)

# the request read: spelled and fitting (each equation used twice)
def cro.done(-s: String, -bn: List<&2, Nat>, -cn: List<&2, Nat>, -s2: String, -b: List<&2, CU.Ent>, -c: List<&2, CU.Ent>, pre: {s == LawsBase.wire_spell_nats(bn, LawsBase.wire_spell_nats(cn, s2)) : String}, fb: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, bn)), LawsBase.wire_nats_fit(bn)) == True{} : Bool}, fc: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cn)), LawsBase.wire_nats_fit(cn)) == True{} : Bool}, +eb: {bn == CatalogUnion.cu_ents(b) : List<&2, Nat>}, +ec: {cn == CatalogUnion.cu_ents(c) : List<&2, Nat>}) -> {s == CatalogUnion.cu_spell_req(FCu.Req{b, c}, s2) : String} & {CatalogUnion.cu_req_fits(FCu.Req{b, c}) == True{} : Bool}:
  (cro.spell(s, bn, cn, s2, b, c, pre, eb, ec), cro.fit(bn, cn, b, c, fb, fc, eb, ec))

def cro.both(+s: String, +bn: List<&2, Nat>, +cn: List<&2, Nat>, +s2: String, pre: {s == LawsBase.wire_spell_nats(bn, LawsBase.wire_spell_nats(cn, s2)) : String}, fb: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, bn)), LawsBase.wire_nats_fit(bn)) == True{} : Bool}, fc: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cn)), LawsBase.wire_nats_fit(cn)) == True{} : Bool}, mb: Maybe<&2, List<&2, CU.Ent>>, hb: cro.EO(bn, mb), mc: Maybe<&2, List<&2, CU.Ent>>, hc: cro.EO(cn, mc)) -> cro.Req(s, FCu.get_req.both(mb, mc, s2)):
  match mb mc:
    case Some{+b} Some{+c}:
      cro.done(s, bn, cn, s2, b, c, pre, fb, fc, hb, hc)
    case Some{b} None{}:
      Unit{}
    case None{} Some{c}:
      Unit{}
    case None{} None{}:
      Unit{}

def cro.c(+s: String, +bn: List<&2, Nat>, +s1: String, pre: {s == LawsBase.wire_spell_nats(bn, s1) : String}, fb: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, bn)), LawsBase.wire_nats_fit(bn)) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, xd: NL.nl.NL(s1, d)) -> cro.Req(s, FCu.get_req.c(bn, d)):
  match d:
    case Wr.Got{+cn, +s2}:
      (e, fc) = xd
      cro.both(s, bn, cn, s2, NL.nl.step(z => LawsBase.wire_spell_nats(bn, z), s, s1, LawsBase.wire_spell_nats(cn, s2), pre, e), fb, fc, FCu.ents.of(bn), cro.eo(bn), FCu.ents.of(cn), cro.eo(cn))
    case Wr.Bad{}:
      Unit{}

def cro.b(+s: String, d: Wr.Dec<List<&2, Nat>>, xd: NL.nl.NL(s, d)) -> cro.Req(s, FCu.get_req.b(d)):
  match d:
    case Wr.Got{+bn, +s1}:
      (e, fb) = xd
      cro.c(s, bn, s1, e, fb, Wr.get_list(~Nat, ~Wr.get_nat, s1), NL.nl.nl(s1))
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def cro.req(+s: String) -> cro.Req(s, FCu.get_req(s)):
  cro.b(s, Wr.get_list(~Nat, ~Wr.get_nat, s), NL.nl.nl(s))

# The entry
# ---------

def cro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FCu.Req, q => {(s, (CatalogUnion.cu_req_fits(q), a)) == (CatalogUnion.cu_spell_req(q, ""), (True{}, CatalogUnion.cu_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def cro.top_eq(+s: String, +q: FCu.Req, +a: String, e: {s == CatalogUnion.cu_spell_req(q, "") : String}, f: {CatalogUnion.cu_req_fits(q) == True{} : Bool}, ea: {a == CatalogUnion.cu_spell_answer(q) : String}) -> {(s, (CatalogUnion.cu_req_fits(q), a)) == (CatalogUnion.cu_spell_req(q, ""), (True{}, CatalogUnion.cu_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, CatalogUnion.cu_spell_req(q, ""), e) : {(_, (CatalogUnion.cu_req_fits(q), a)) == (CatalogUnion.cu_spell_req(q, ""), (True{}, CatalogUnion.cu_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, CatalogUnion.cu_req_fits(q), True{}, f) : {(CatalogUnion.cu_spell_req(q, ""), (_, a)) == (CatalogUnion.cu_spell_req(q, ""), (True{}, CatalogUnion.cu_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, CatalogUnion.cu_spell_answer(q), ea) : {(CatalogUnion.cu_spell_req(q, ""), (True{}, _)) == (CatalogUnion.cu_spell_req(q, ""), (True{}, CatalogUnion.cu_spell_answer(q))) : String & (Bool & String)}
  {==}

# the entry's reply to a request read whole is the spelled union
def cro.ans(q: FCu.Req) -> {FCu.reply(True{}, q) == CatalogUnion.cu_spell_answer(q) : String}:
  match q:
    case FCu.Req{+b, +c}:
      PCatalogUnionFfiAnswersSpelled.cua.reply(b, c)

# the end check: nothing left answers the request, anything left is the
# error form
def cro.fin(+s: String, +q: FCu.Req, r: String, pre: {s == CatalogUnion.cu_spell_req(q, r) : String}, f: {CatalogUnion.cu_req_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FCu.reply(Wr.end(r), q)) == False{} : Bool}) -> cro.G(s, FCu.reply(Wr.end(r), q)):
  match r:
    case SNil{}:
      (q, cro.top_eq(s, q, FCu.reply(True{}, q), pre, f, cro.ans(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(cro.G(s, FCu.reply(False{}, q)), ok)

def cro.main(+s: String, d: Wr.Dec<FCu.Req>, inv: cro.Req(s, d), ok: {LawsBase.wire_opens_err(FCu.answer(d)) == False{} : Bool}) -> cro.G(s, FCu.answer(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      cro.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cro.G(s, Wr.err("catalog_union: malformed request")), ok)

def CatalogUnion.catalog_union_ffi_reads_only_requests(s, ok):
  cro.main(s, FCu.get_req(s), cro.req(s), ok)
