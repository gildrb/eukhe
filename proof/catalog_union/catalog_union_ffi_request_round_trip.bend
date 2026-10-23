# eukhe: the proof of LAW catalog_union_ffi_request_round_trip

import Base
import ../../bend/catalog_union.bend as CU
import ../../bend/ffi_catalog_union.bend as FCu
import ../../bend/wire.bend as Wr
import ../../laws/catalog_union.bend as CatalogUnion
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# catalog_union
# -------------

def fe.opt_rt(m: Maybe<&2, Nat>) -> {m == FCu.opt.of(FCu.opt(m)) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def fe.ents_of(es: List<&2, CU.Ent>) -> {FCu.ents.of(FCu.ents(es)) == Some{es} : Maybe<&2, List<&2, CU.Ent>>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case CU.Ent{+k, +a, +d, +t, +c, +f, +h}:
          %Equal.sym(Maybe<&2, List<&2, CU.Ent>>, FCu.ents.of(FCu.ents(rest)), Some{rest}, fe.ents_of(rest)) : {FCu.ents.cons(CU.Ent{k, a, d, FCu.opt.of(FCu.opt(t)), FCu.opt.of(FCu.opt(c)), FCu.opt.of(FCu.opt(f)), FCu.opt.of(FCu.opt(h))}, _) == Some{CU.Ent{k, a, d, t, c, f, h} <> rest} : Maybe<&2, List<&2, CU.Ent>>}
          %fe.opt_rt(t) : {Some{CU.Ent{k, a, d, _, FCu.opt.of(FCu.opt(c)), FCu.opt.of(FCu.opt(f)), FCu.opt.of(FCu.opt(h))} <> rest} == Some{CU.Ent{k, a, d, t, c, f, h} <> rest} : Maybe<&2, List<&2, CU.Ent>>}
          %fe.opt_rt(c) : {Some{CU.Ent{k, a, d, t, _, FCu.opt.of(FCu.opt(f)), FCu.opt.of(FCu.opt(h))} <> rest} == Some{CU.Ent{k, a, d, t, c, f, h} <> rest} : Maybe<&2, List<&2, CU.Ent>>}
          %fe.opt_rt(f) : {Some{CU.Ent{k, a, d, t, c, _, FCu.opt.of(FCu.opt(h))} <> rest} == Some{CU.Ent{k, a, d, t, c, f, h} <> rest} : Maybe<&2, List<&2, CU.Ent>>}
          %fe.opt_rt(h) : {Some{CU.Ent{k, a, d, t, c, f, _} <> rest} == Some{CU.Ent{k, a, d, t, c, f, h} <> rest} : Maybe<&2, List<&2, CU.Ent>>}
          {==}

def CatalogUnion.catalog_union_ffi_request_round_trip(bs, cs, rest, h0):
  +h = h0
  +hb = LLogicBool.wr_and_l(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(bs))), LawsBase.wire_nats_fit(FCu.ents(bs))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(cs))), LawsBase.wire_nats_fit(FCu.ents(cs))), h)
  +hc = LLogicBool.wr_and_r(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(bs))), LawsBase.wire_nats_fit(FCu.ents(bs))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FCu.ents(cs))), LawsBase.wire_nats_fit(FCu.ents(cs))), h)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, FCu.ents(bs), FCu.put_ns(FCu.ents(cs), rest))), Wr.Got{FCu.ents(bs), FCu.put_ns(FCu.ents(cs), rest)}, Wire.wire_list_round_trip(FCu.ents(bs), FCu.put_ns(FCu.ents(cs), rest), hb)) : {FCu.get_req.b(_) == Wr.Got{FCu.Req{bs, cs}, rest} : Wr.Dec<FCu.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, FCu.ents(cs), rest)), Wr.Got{FCu.ents(cs), rest}, Wire.wire_list_round_trip(FCu.ents(cs), rest, hc)) : {FCu.get_req.c(FCu.ents(bs), _) == Wr.Got{FCu.Req{bs, cs}, rest} : Wr.Dec<FCu.Req>}
  %Equal.sym(Maybe<&2, List<&2, CU.Ent>>, FCu.ents.of(FCu.ents(bs)), Some{bs}, fe.ents_of(bs)) : {FCu.get_req.both(_, FCu.ents.of(FCu.ents(cs)), rest) == Wr.Got{FCu.Req{bs, cs}, rest} : Wr.Dec<FCu.Req>}
  %Equal.sym(Maybe<&2, List<&2, CU.Ent>>, FCu.ents.of(FCu.ents(cs)), Some{cs}, fe.ents_of(cs)) : {FCu.get_req.both(Some{bs}, _, rest) == Wr.Got{FCu.Req{bs, cs}, rest} : Wr.Dec<FCu.Req>}
  {==}
