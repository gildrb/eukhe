# eukhe: the proof of LAW work_left_entry_exact
#
# PROOF: each stage of the decoder answers a field only for an input that
# spells it before what follows (Wire.wire_nat_exact, Wire.wire_bool_exact),
# a count only when it fits the wire (Wire.wire_nat_decoded_fits), and an
# unknown tag never; so a request the decoder reads is the spec's spelling
# of the facts it read before the rest (wx.driven). The entry answers a step
# only for a request read whole with nothing left (wx.top).

import Base
import ../../bend/progress.bend as Pg
import ../../bend/work_left.bend as Wl
import ../../bend/ffi_work_left.bend as FWl
import ../../bend/wire.bend as Wr
import ../../spec/agents/work_left.bend as SpL
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/work_left.bend as WorkLeft
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../base/staging.bend as LStg
import ../base/wire_dec.bend as LE

# the facts a decoder stage answered for the input s: s is their spelling
# before the rest, and their counts fit the wire
def wx.P(s: String, d: Wr.Dec<Wl.Facts>) -> Type:
  match d:
    case Wr.Got{f, rest}:
      {s == SpL.w_req(f, rest) : String} & {WorkLeft.wl_fits(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# the count of a progress check fits the wire (the decoder never reads a
# steer)
def wx.sf(st: Pg.Run) -> Bool:
  match st:
    case Pg.Go{k}:
      LawsBase.wire_fits(k)
    case Pg.Stop{k}:
      LawsBase.wire_fits(k)
    case Pg.Steer{k}:
      False{}

# the tag of a progress check that stops, or goes on
def wx.tag(stop: Bool) -> Nat:
  match stop:
    case True{}:
      1n
    case False{}:
      0n

def wx.and_tt(+a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      LStg.stg.absurdF({Bool.and(False{}, b) == True{} : Bool}, ha)

def wx.fits(-d: Bool, -q: Bool, -a: Bool, -b: Bool, st: Pg.Run, +n: Nat, -r: Wl.Reading, hn: {LawsBase.wire_fits(n) == True{} : Bool}, hs: {wx.sf(st) == True{} : Bool}) -> {WorkLeft.wl_fits(Wl.Facts{d, q, a, b, st, n, r}) == True{} : Bool}:
  match st:
    case Pg.Go{+k}:
      wx.and_tt(LawsBase.wire_fits(n), LawsBase.wire_fits(k), hn, hs)
    case Pg.Stop{+k}:
      wx.and_tt(LawsBase.wire_fits(n), LawsBase.wire_fits(k), hn, hs)
    case Pg.Steer{+k}:
      LStg.stg.absurdF({WorkLeft.wl_fits(Wl.Facts{d, q, a, b, Pg.Steer{k}, n, r}) == True{} : Bool}, hs)

# s spells the fields before the reading; r7 spells the reading: s is the
# request
def wx.join(-s: String, +d: Bool, +q: Bool, +a: Bool, +b: Bool, +st: Pg.Run, +n: Nat, +r7: String, +rd: Wl.Reading, +rest: String, pre: {s == Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, SpL.w_stall(st, Wr.put_nat(n, r7)))))) : String}, e: {r7 == SpL.w_reading(rd, rest) : String}) -> {s == SpL.w_req(Wl.Facts{d, q, a, b, st, n, rd}, rest) : String}:
  Equal.trans(String, s, Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, SpL.w_stall(st, Wr.put_nat(n, r7)))))), Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, SpL.w_stall(st, Wr.put_nat(n, SpL.w_reading(rd, rest))))))), pre, Equal.cong(String, String, z => Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, SpL.w_stall(st, Wr.put_nat(n, z)))))), r7, SpL.w_reading(rd, rest), e))

def wx.reading(-s: String, +d: Bool, +q: Bool, +a: Bool, +b: Bool, +st: Pg.Run, +n: Nat, +r7: String, x: Wr.Dec<Nat>, ex: {Wr.get_nat(r7) == x : Wr.Dec<Nat>}, pre: {s == Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, SpL.w_stall(st, Wr.put_nat(n, r7)))))) : String}, hn: {LawsBase.wire_fits(n) == True{} : Bool}, hs: {wx.sf(st) == True{} : Bool}) -> wx.P(s, FWl.get_facts.reading(d, q, a, b, st, n, FWl.get_reading(x))):
  match x:
    case Wr.Got{t, +rest}:
      match t:
        case 0n:
          (wx.join(s, d, q, a, b, st, n, r7, Wl.Unread{}, rest, pre, Wire.wire_nat_exact(r7, 0n, rest, ex)), wx.fits(d, q, a, b, st, n, Wl.Unread{}, hn, hs))
        case 1n:
          (wx.join(s, d, q, a, b, st, n, r7, Wl.Finished{}, rest, pre, Wire.wire_nat_exact(r7, 1n, rest, ex)), wx.fits(d, q, a, b, st, n, Wl.Finished{}, hn, hs))
        case 2n:
          (wx.join(s, d, q, a, b, st, n, r7, Wl.Left{}, rest, pre, Wire.wire_nat_exact(r7, 2n, rest, ex)), wx.fits(d, q, a, b, st, n, Wl.Left{}, hn, hs))
        case 3n:
          (wx.join(s, d, q, a, b, st, n, r7, Wl.Unjudged{}, rest, pre, Wire.wire_nat_exact(r7, 3n, rest, ex)), wx.fits(d, q, a, b, st, n, Wl.Unjudged{}, hn, hs))
        case 4n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def wx.left(-s: String, +d: Bool, +q: Bool, +a: Bool, +b: Bool, +st: Pg.Run, +r6: String, x: Wr.Dec<Nat>, +ex: {Wr.get_nat(r6) == x : Wr.Dec<Nat>}, pre: {s == Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, SpL.w_stall(st, r6))))) : String}, hs: {wx.sf(st) == True{} : Bool}) -> wx.P(s, FWl.get_facts.left(d, q, a, b, st, x)):
  match x:
    case Wr.Got{+n, +r7}:
      +e = Wire.wire_nat_exact(r6, n, r7, ex)
      +pre2 = Equal.trans(String, s, Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, SpL.w_stall(st, r6))))), Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, SpL.w_stall(st, Wr.put_nat(n, r7)))))), pre, Equal.cong(String, String, z => Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, SpL.w_stall(st, z))))), r6, Wr.put_nat(n, r7), e))
      wx.reading(s, d, q, a, b, st, n, r7, Wr.get_nat(r7), {==}, pre2, Wire.wire_nat_decoded_fits(r6, n, r7, ex), hs)
    case Wr.Bad{}:
      Unit{}

def wx.count(-s: String, +d: Bool, +q: Bool, +a: Bool, +b: Bool, stop: Bool, +r5: String, +r6: String, e5: {r5 == Wr.put_nat(wx.tag(stop), r6) : String}, y: Wr.Dec<Nat>, +ey: {Wr.get_nat(r6) == y : Wr.Dec<Nat>}, pre: {s == Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, r5)))) : String}) -> wx.P(s, FWl.get_facts.stall(d, q, a, b, FWl.get_stall.count(stop, y))):
  match stop:
    case True{}:
      match y:
        case Wr.Got{+k, +r7}:
          +e6 = Wire.wire_nat_exact(r6, k, r7, ey)
          +e5b = LE.dcw.after(r5, 1n, r6, Wr.put_nat(k, r7), e5, e6)
          +pre2 = Equal.trans(String, s, Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, r5)))), Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, Wr.put_nat(1n, Wr.put_nat(k, r7)))))), pre, Equal.cong(String, String, z => Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, z)))), r5, Wr.put_nat(1n, Wr.put_nat(k, r7)), e5b))
          wx.left(s, d, q, a, b, Pg.Stop{k}, r7, Wr.get_nat(r7), {==}, pre2, Wire.wire_nat_decoded_fits(r6, k, r7, ey))
        case Wr.Bad{}:
          Unit{}
    case False{}:
      match y:
        case Wr.Got{+k, +r7}:
          +e6 = Wire.wire_nat_exact(r6, k, r7, ey)
          +e5b = LE.dcw.after(r5, 0n, r6, Wr.put_nat(k, r7), e5, e6)
          +pre2 = Equal.trans(String, s, Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, r5)))), Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, Wr.put_nat(0n, Wr.put_nat(k, r7)))))), pre, Equal.cong(String, String, z => Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, z)))), r5, Wr.put_nat(0n, Wr.put_nat(k, r7)), e5b))
          wx.left(s, d, q, a, b, Pg.Go{k}, r7, Wr.get_nat(r7), {==}, pre2, Wire.wire_nat_decoded_fits(r6, k, r7, ey))
        case Wr.Bad{}:
          Unit{}

def wx.stall(-s: String, +d: Bool, +q: Bool, +a: Bool, +b: Bool, +r5: String, x: Wr.Dec<Nat>, ex: {Wr.get_nat(r5) == x : Wr.Dec<Nat>}, pre: {s == Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, r5)))) : String}) -> wx.P(s, FWl.get_facts.stall(d, q, a, b, FWl.get_stall(x))):
  match x:
    case Wr.Got{t, +r6}:
      match t:
        case 0n:
          wx.count(s, d, q, a, b, False{}, r5, r6, Wire.wire_nat_exact(r5, 0n, r6, ex), Wr.get_nat(r6), {==}, pre)
        case 1n:
          wx.count(s, d, q, a, b, True{}, r5, r6, Wire.wire_nat_exact(r5, 1n, r6, ex), Wr.get_nat(r6), {==}, pre)
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def wx.funded(-s: String, +d: Bool, +q: Bool, +a: Bool, +r4: String, x: Wr.Dec<Bool>, +ex: {Wr.get_bool(r4) == x : Wr.Dec<Bool>}, pre: {s == Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, r4))) : String}) -> wx.P(s, FWl.get_facts.funded(d, q, a, x)):
  match x:
    case Wr.Got{+b, +r5}:
      +e = Wire.wire_bool_exact(r4, b, r5, ex)
      +pre2 = Equal.trans(String, s, Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, r4))), Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, r5)))), pre, Equal.cong(String, String, z => Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, z))), r4, Wr.put_bool(b, r5), e))
      wx.stall(s, d, q, a, b, r5, Wr.get_nat(r5), {==}, pre2)
    case Wr.Bad{}:
      Unit{}

def wx.acted(-s: String, +d: Bool, +q: Bool, +r3: String, x: Wr.Dec<Bool>, +ex: {Wr.get_bool(r3) == x : Wr.Dec<Bool>}, pre: {s == Wr.put_bool(d, Wr.put_bool(q, r3)) : String}) -> wx.P(s, FWl.get_facts.acted(d, q, x)):
  match x:
    case Wr.Got{+a, +r4}:
      +e = Wire.wire_bool_exact(r3, a, r4, ex)
      +pre2 = Equal.trans(String, s, Wr.put_bool(d, Wr.put_bool(q, r3)), Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, r4))), pre, Equal.cong(String, String, z => Wr.put_bool(d, Wr.put_bool(q, z)), r3, Wr.put_bool(a, r4), e))
      wx.funded(s, d, q, a, r4, Wr.get_bool(r4), {==}, pre2)
    case Wr.Bad{}:
      Unit{}

def wx.queued(-s: String, +d: Bool, +r2: String, x: Wr.Dec<Bool>, +ex: {Wr.get_bool(r2) == x : Wr.Dec<Bool>}, pre: {s == Wr.put_bool(d, r2) : String}) -> wx.P(s, FWl.get_facts.queued(d, x)):
  match x:
    case Wr.Got{+q, +r3}:
      +e = Wire.wire_bool_exact(r2, q, r3, ex)
      +pre2 = Equal.trans(String, s, Wr.put_bool(d, r2), Wr.put_bool(d, Wr.put_bool(q, r3)), pre, Equal.cong(String, String, z => Wr.put_bool(d, z), r2, Wr.put_bool(q, r3), e))
      wx.acted(s, d, q, r3, Wr.get_bool(r3), {==}, pre2)
    case Wr.Bad{}:
      Unit{}

def wx.driven(+s: String, x: Wr.Dec<Bool>, +ex: {Wr.get_bool(s) == x : Wr.Dec<Bool>}) -> wx.P(s, FWl.get_facts.driven(x)):
  match x:
    case Wr.Got{+d, +r2}:
      wx.queued(s, d, r2, Wr.get_bool(r2), {==}, Wire.wire_bool_exact(s, d, r2, ex))
    case Wr.Bad{}:
      Unit{}

# a step answered: a request read whole, nothing left
def wx.top(-s: String, d: Wr.Dec<Wl.Facts>, rp: wx.P(s, d), ok: {LawsBase.wire_opens_err(FWl.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, Wl.Facts, f => {s == SpL.w_req(f, "") : String} & {WorkLeft.wl_fits(f) == True{} : Bool}>:
  match d:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          (f, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, Wl.Facts, f => {s == SpL.w_req(f, "") : String} & {WorkLeft.wl_fits(f) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, Wl.Facts, f => {s == SpL.w_req(f, "") : String} & {WorkLeft.wl_fits(f) == True{} : Bool}>, ok)

def WorkLeft.work_left_entry_exact(s, ok):
  wx.top(s, FWl.get_facts(s), wx.driven(s, Wr.get_bool(s), {==}), ok)
