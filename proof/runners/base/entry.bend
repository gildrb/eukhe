# eukhe: lemmas the proofs of the runners entry share (laws/runners.bend,
# section runners entry): the entry spells the model's decision as the
# laws do, and its reader reads back every request Rust writes

import Base
import ../../../bend/ffi_runners.bend as FRu
import ../../../bend/runners.bend as Ru
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/runners.bend as Runners
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire

# The entry answers as the laws spell the model's decision
# --------------------------------------------------------

def rn.out(o: Ru.Out) -> {FRu.put_out(o, "") == Runners.spell_out(o) : String}:
  match o:
    case Ru.Out{a, e}:
      match e:
        case Ru.Ran{h}:
          match h:
            case Ru.Auto{}:
              {==}
            case Ru.Approved{}:
              {==}
        case Ru.Refused{w}:
          match w:
            case Ru.Denied{}:
              {==}
            case Ru.Unanswered{}:
              {==}

def rn.reply(q: FRu.Req) -> {FRu.answer(q) == Runners.spell_answer(q) : String}:
  match q:
    case FRu.QWithin{c, a}:
      {==}
    case FRu.QCell{+c, +a, +k}:
      rn.out(Ru.cell(c, a, k))
    case FRu.QRegistry{}:
      {==}
    case FRu.QMain{h}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}

# The entry's reader reads back what Rust writes
# ----------------------------------------------

def rn.rt_asker(k: Ru.Asker, rest: String) -> {FRu.get_asker(Wr.get_nat(Runners.spell_asker(k, rest))) == Wr.Got{k, rest} : Wr.Dec<Ru.Asker>}:
  match k:
    case Ru.NoClient{}:
      {==}
    case Ru.Silent{}:
      {==}
    case Ru.Says{y}:
      match y:
        case True{}:
          {==}
        case False{}:
          {==}

def rn.rt_within(+c: List<&2, Nat>, +a: List<&2, Nat>, +rest: String, +fits: {Runners.req_fits(FRu.QWithin{c, a}) == True{} : Bool}) -> {FRu.get_req(Runners.spell_req(FRu.QWithin{c, a}, rest)) == Wr.Got{FRu.QWithin{c, a}, rest} : Wr.Dec<FRu.Req>}:
  +hc = LLogicBool.wr_and_l(Runners.ns_fit(c), Runners.ns_fit(a), fits)
  +ha = LLogicBool.wr_and_r(Runners.ns_fit(c), Runners.ns_fit(a), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Runners.spell_ns(c, Runners.spell_ns(a, rest))), Wr.Got{c, Runners.spell_ns(a, rest)}, Wire.wire_list_round_trip(c, Runners.spell_ns(a, rest), hc)) : {FRu.get_within(_) == Wr.Got{FRu.QWithin{c, a}, rest} : Wr.Dec<FRu.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Runners.spell_ns(a, rest)), Wr.Got{a, rest}, Wire.wire_list_round_trip(a, rest, ha)) : {FRu.get_within.auto(c, _) == Wr.Got{FRu.QWithin{c, a}, rest} : Wr.Dec<FRu.Req>}
  {==}

def rn.rt_cell(+c: List<&2, Nat>, +a: List<&2, Nat>, +k: Ru.Asker, +rest: String, +fits: {Runners.req_fits(FRu.QCell{c, a, k}) == True{} : Bool}) -> {FRu.get_req(Runners.spell_req(FRu.QCell{c, a, k}, rest)) == Wr.Got{FRu.QCell{c, a, k}, rest} : Wr.Dec<FRu.Req>}:
  +hc = LLogicBool.wr_and_l(Runners.ns_fit(c), Runners.ns_fit(a), fits)
  +ha = LLogicBool.wr_and_r(Runners.ns_fit(c), Runners.ns_fit(a), fits)
  +r2 = Runners.spell_asker(k, rest)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Runners.spell_ns(c, Runners.spell_ns(a, r2))), Wr.Got{c, Runners.spell_ns(a, r2)}, Wire.wire_list_round_trip(c, Runners.spell_ns(a, r2), hc)) : {FRu.get_cell(_) == Wr.Got{FRu.QCell{c, a, k}, rest} : Wr.Dec<FRu.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Runners.spell_ns(a, r2)), Wr.Got{a, r2}, Wire.wire_list_round_trip(a, r2, ha)) : {FRu.get_cell.auto(c, _) == Wr.Got{FRu.QCell{c, a, k}, rest} : Wr.Dec<FRu.Req>}
  %Equal.sym(Wr.Dec<Ru.Asker>, FRu.get_asker(Wr.get_nat(r2)), Wr.Got{k, rest}, rn.rt_asker(k, rest)) : {FRu.get_cell.asker(c, a, _) == Wr.Got{FRu.QCell{c, a, k}, rest} : Wr.Dec<FRu.Req>}
  {==}

def rn.rt_main(h: Bool, rest: String) -> {FRu.get_req(Runners.spell_req(FRu.QMain{h}, rest)) == Wr.Got{FRu.QMain{h}, rest} : Wr.Dec<FRu.Req>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def rn.rt(q: FRu.Req, +rest: String, fits: {Runners.req_fits(q) == True{} : Bool}) -> {FRu.get_req(Runners.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FRu.Req>}:
  match q:
    case FRu.QWithin{c, a}:
      rn.rt_within(c, a, rest, fits)
    case FRu.QCell{c, a, k}:
      rn.rt_cell(c, a, k, rest, fits)
    case FRu.QRegistry{}:
      {==}
    case FRu.QMain{h}:
      rn.rt_main(h, rest)
