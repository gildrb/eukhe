# eukhe: lemmas of the entry proofs of area undo (bend/ffi_undo.bend): a
# spelled request that fits reads back whole (unq.req: the tag and each
# Nat by wire_nat_round_trip, each list of Nats by wire_nats_spells and
# wire_list_round_trip, the rows by LA.unb.rows_back)

import Base
import ../../../bend/undo.bend as U
import ../../../bend/ffi_undo.bend as FU
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/undo.bend as Undo
import ../../../laws/wire.bend as Wire
import ../../base/wire.bend as LWire
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../../base/logic/bool.bend as LLogicBool
import ../base.bend as LA

def unq.step(+l: List<&2, Nat>, +b: Maybe<&2, Nat>, +e: U.Ev, +rest: String, h: {Undo.sp_fit_req(FU.QStep{U.St{l, b}, e}) == True{} : Bool}) -> {FU.get_req(Undo.sp_w_req(FU.QStep{U.St{l, b}, e}, rest)) == Wr.Got{FU.QStep{U.St{l, b}, e}, rest} : Wr.Dec<FU.Req>}:
  +wb = Undo.sp_w_maybe(b)
  +we = Undo.sp_w_ev(e)
  +z = Wr.put_nat(we, rest)
  +y = Wr.put_nat(wb, z)
  +x = LawsBase.wire_spell_nats(l, y)
  +hq = h
  +fl = LLogicBool.tree.pt.and_l(Undo.sp_fit_nats(l), Bool.and(LawsBase.wire_fits(wb), LawsBase.wire_fits(we)), hq)
  +fr = LLogicBool.tree.pt.and_r(Undo.sp_fit_nats(l), Bool.and(LawsBase.wire_fits(wb), LawsBase.wire_fits(we)), hq)
  +fb = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(wb), LawsBase.wire_fits(we), fr)
  +fe = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(wb), LawsBase.wire_fits(we), fr)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, x)), Wr.Got{0n, x}, Wire.wire_nat_round_trip(0n, x, {==})) : {FU.get_req.tag(_) == Wr.Got{FU.QStep{U.St{l, b}, e}, rest} : Wr.Dec<FU.Req>}
  %Wire.wire_nats_spells(l, y) : {FU.get_req.live(Wr.get_list(~Nat, ~Wr.get_nat, _)) == Wr.Got{FU.QStep{U.St{l, b}, e}, rest} : Wr.Dec<FU.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, l, y)), Wr.Got{l, y}, Wire.wire_list_round_trip(l, y, fl)) : {FU.get_req.live(_) == Wr.Got{FU.QStep{U.St{l, b}, e}, rest} : Wr.Dec<FU.Req>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(y), Wr.Got{wb, z}, Wire.wire_nat_round_trip(wb, z, fb)) : {FU.get_req.base(l, _) == Wr.Got{FU.QStep{U.St{l, b}, e}, rest} : Wr.Dec<FU.Req>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(z), Wr.Got{we, rest}, Wire.wire_nat_round_trip(we, rest, fe)) : {FU.get_req.ev(l, wb, _) == Wr.Got{FU.QStep{U.St{l, b}, e}, rest} : Wr.Dec<FU.Req>}
  %Equal.sym(Maybe<&2, Nat>, FU.maybe_of(wb), b, LA.unb.mw(b)) : {Wr.Got{FU.QStep{U.St{l, _}, FU.ev_of(we)}, rest} == Wr.Got{FU.QStep{U.St{l, b}, e}, rest} : Wr.Dec<FU.Req>}
  %Equal.sym(U.Ev, FU.ev_of(we), e, LA.unb.ew(e)) : {Wr.Got{FU.QStep{U.St{l, b}, _}, rest} == Wr.Got{FU.QStep{U.St{l, b}, e}, rest} : Wr.Dec<FU.Req>}
  {==}


def unq.fix(+rows: List<&2, U.Row>, +rest: String, h: {Undo.sp_fit_nats(Undo.sp_flat(rows)) == True{} : Bool}) -> {FU.get_req(Undo.sp_w_req(FU.QFix{rows}, rest)) == Wr.Got{FU.QFix{rows}, rest} : Wr.Dec<FU.Req>}:
  +f = Undo.sp_flat(rows)
  +x = LawsBase.wire_spell_nats(f, rest)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, x)), Wr.Got{1n, x}, Wire.wire_nat_round_trip(1n, x, {==})) : {FU.get_req.tag(_) == Wr.Got{FU.QFix{rows}, rest} : Wr.Dec<FU.Req>}
  %Wire.wire_nats_spells(f, rest) : {FU.get_req.fix_rows(Wr.get_list(~Nat, ~Wr.get_nat, _)) == Wr.Got{FU.QFix{rows}, rest} : Wr.Dec<FU.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, f, rest)), Wr.Got{f, rest}, Wire.wire_list_round_trip(f, rest, h)) : {FU.get_req.fix_rows(_) == Wr.Got{FU.QFix{rows}, rest} : Wr.Dec<FU.Req>}
  %Equal.sym(Maybe<&2, List<&2, U.Row>>, FU.rows_of(f), Some{rows}, LA.unb.rows_back(rows)) : {FU.get_req.fix(_, rest) == Wr.Got{FU.QFix{rows}, rest} : Wr.Dec<FU.Req>}
  {==}

def unq.seen(+rows: List<&2, U.Row>, +rest: String, h: {Undo.sp_fit_nats(Undo.sp_flat(rows)) == True{} : Bool}) -> {FU.get_req(Undo.sp_w_req(FU.QSeen{rows}, rest)) == Wr.Got{FU.QSeen{rows}, rest} : Wr.Dec<FU.Req>}:
  +f = Undo.sp_flat(rows)
  +x = LawsBase.wire_spell_nats(f, rest)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, x)), Wr.Got{2n, x}, Wire.wire_nat_round_trip(2n, x, {==})) : {FU.get_req.tag(_) == Wr.Got{FU.QSeen{rows}, rest} : Wr.Dec<FU.Req>}
  %Wire.wire_nats_spells(f, rest) : {FU.get_req.seen_rows(Wr.get_list(~Nat, ~Wr.get_nat, _)) == Wr.Got{FU.QSeen{rows}, rest} : Wr.Dec<FU.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, f, rest)), Wr.Got{f, rest}, Wire.wire_list_round_trip(f, rest, h)) : {FU.get_req.seen_rows(_) == Wr.Got{FU.QSeen{rows}, rest} : Wr.Dec<FU.Req>}
  %Equal.sym(Maybe<&2, List<&2, U.Row>>, FU.rows_of(f), Some{rows}, LA.unb.rows_back(rows)) : {FU.get_req.seen(_, rest) == Wr.Got{FU.QSeen{rows}, rest} : Wr.Dec<FU.Req>}
  {==}

# a spelled request that fits reads back, the input after it untouched
def unq.req(q: FU.Req, +rest: String, h: {Undo.sp_fit_req(q) == True{} : Bool}) -> {FU.get_req(Undo.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FU.Req>}:
  match q:
    case FU.QStep{st, +e}:
      match st:
        case U.St{+l, +b}:
          unq.step(l, b, e, rest, h)
    case FU.QFix{+rows}:
      unq.fix(rows, rest, h)
    case FU.QSeen{+rows}:
      unq.seen(rows, rest, h)
