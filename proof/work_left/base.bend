# eukhe: lemmas the proofs of area work_left share: the entry's decoder
# reads a request spelled by the spec (spec/agents/work_left.bend), its
# counts within the wire, back whole; the entry spells a step as the spec
# does

import Base
import ../../bend/progress.bend as Pg
import ../../bend/work_left.bend as Wl
import ../../bend/ffi_work_left.bend as FWl
import ../../bend/wire.bend as Wr
import ../../spec/agents/work_left.bend as SpL
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/work_left.bend as WorkLeft
import ../base/logic/bool.bend as LLogicBool

# Read back
# ---------

def wl.reading_rt(r: Wl.Reading, -rest: String) -> {FWl.get_reading(Wr.get_nat(SpL.w_reading(r, rest))) == Wr.Got{r, rest} : Wr.Dec<Wl.Reading>}:
  match r:
    case Wl.Unread{}:
      {==}
    case Wl.Finished{}:
      {==}
    case Wl.Left{}:
      {==}
    case Wl.Unjudged{}:
      {==}

def wl.go_rt(+k: Nat, +rest: String, h: {LawsBase.wire_fits(k) == True{} : Bool}) -> {FWl.get_stall(Wr.get_nat(SpL.w_stall(Pg.Go{k}, rest))) == Wr.Got{Pg.Go{k}, rest} : Wr.Dec<Pg.Goal>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(k, rest)), Wr.Got{k, rest}, Wire.wire_nat_round_trip(k, rest, h)) : {FWl.get_stall.count(False{}, _) == Wr.Got{Pg.Go{k}, rest} : Wr.Dec<Pg.Goal>}
  {==}

def wl.stop_rt(+k: Nat, +rest: String, h: {LawsBase.wire_fits(k) == True{} : Bool}) -> {FWl.get_stall(Wr.get_nat(SpL.w_stall(Pg.Stop{k}, rest))) == Wr.Got{Pg.Stop{k}, rest} : Wr.Dec<Pg.Goal>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(k, rest)), Wr.Got{k, rest}, Wire.wire_nat_round_trip(k, rest, h)) : {FWl.get_stall.count(True{}, _) == Wr.Got{Pg.Stop{k}, rest} : Wr.Dec<Pg.Goal>}
  {==}

# a spelled request reads back (with the entry's decoder), the rest
# untouched, when its progress check reads back (hs) and its steps fit the
# wire (hn)
def wl.req_rt.at(+d: Bool, +q: Bool, +a: Bool, +b: Bool, +s: Pg.Goal, +n: Nat, +r: Wl.Reading, +rest: String, hs: {FWl.get_stall(Wr.get_nat(SpL.w_stall(s, Wr.put_nat(n, SpL.w_reading(r, rest))))) == Wr.Got{s, Wr.put_nat(n, SpL.w_reading(r, rest))} : Wr.Dec<Pg.Goal>}, hn: {LawsBase.wire_fits(n) == True{} : Bool}) -> {FWl.get_facts(SpL.w_req(Wl.Facts{d, q, a, b, s, n, r}, rest)) == Wr.Got{Wl.Facts{d, q, a, b, s, n, r}, rest} : Wr.Dec<Wl.Facts>}:
  +r8 = SpL.w_reading(r, rest)
  +r7 = Wr.put_nat(n, r8)
  +r6 = SpL.w_stall(s, r7)
  +r5 = Wr.put_bool(b, r6)
  +r4 = Wr.put_bool(a, r5)
  +r3 = Wr.put_bool(q, r4)
  +r2 = Wr.put_bool(d, r3)
  -qq = {Wr.Got{Wl.Facts{d, q, a, b, s, n, r}, rest} : Wr.Dec<Wl.Facts>}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r2), Wr.Got{d, r3}, Wire.wire_bool_round_trip(d, r3)) : {FWl.get_facts.driven(_) == qq : Wr.Dec<Wl.Facts>}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r3), Wr.Got{q, r4}, Wire.wire_bool_round_trip(q, r4)) : {FWl.get_facts.queued(d, _) == qq : Wr.Dec<Wl.Facts>}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r4), Wr.Got{a, r5}, Wire.wire_bool_round_trip(a, r5)) : {FWl.get_facts.acted(d, q, _) == qq : Wr.Dec<Wl.Facts>}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r5), Wr.Got{b, r6}, Wire.wire_bool_round_trip(b, r6)) : {FWl.get_facts.funded(d, q, a, _) == qq : Wr.Dec<Wl.Facts>}
  %Equal.sym(Wr.Dec<Pg.Goal>, FWl.get_stall(Wr.get_nat(r6)), Wr.Got{s, r7}, hs) : {FWl.get_facts.stall(d, q, a, b, _) == qq : Wr.Dec<Wl.Facts>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(r7), Wr.Got{n, r8}, Wire.wire_nat_round_trip(n, r8, hn)) : {FWl.get_facts.left(d, q, a, b, s, _) == qq : Wr.Dec<Wl.Facts>}
  %Equal.sym(Wr.Dec<Wl.Reading>, FWl.get_reading(Wr.get_nat(r8)), Wr.Got{r, rest}, wl.reading_rt(r, rest)) : {FWl.get_facts.reading(d, q, a, b, s, n, _) == qq : Wr.Dec<Wl.Facts>}
  {==}

# a spelled request whose counts fit the wire reads back whole, the rest
# untouched
def wl.req_rt(+f: Wl.Facts, +rest: String, +fits: {WorkLeft.wl_fits(f) == True{} : Bool}) -> {FWl.get_facts(SpL.w_req(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Wl.Facts>}:
  match f:
    case Wl.Facts{+d, +q, +a, +b, s, +n, +r}:
      match s:
        case Pg.Go{+k}:
          +r7 = Wr.put_nat(n, SpL.w_reading(r, rest))
          wl.req_rt.at(d, q, a, b, Pg.Go{k}, n, r, rest, wl.go_rt(k, r7, LLogicBool.wr_and_r(LawsBase.wire_fits(n), LawsBase.wire_fits(k), fits)), LLogicBool.wr_and_l(LawsBase.wire_fits(n), LawsBase.wire_fits(k), fits))
        case Pg.Stop{+k}:
          +r7 = Wr.put_nat(n, SpL.w_reading(r, rest))
          wl.req_rt.at(d, q, a, b, Pg.Stop{k}, n, r, rest, wl.stop_rt(k, r7, LLogicBool.wr_and_r(LawsBase.wire_fits(n), LawsBase.wire_fits(k), fits)), LLogicBool.wr_and_l(LawsBase.wire_fits(n), LawsBase.wire_fits(k), fits))

# The reply
# ---------

# the entry spells a step as the spec does
def wl.put(s: Wl.Step, -rest: String) -> {FWl.put_step(s, rest) == SpL.w_step(s, rest) : String}:
  match s:
    case Wl.Continue{m}:
      {==}
    case Wl.Yield{}:
      {==}
    case Wl.Ask{}:
      {==}
