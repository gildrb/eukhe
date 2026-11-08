# eukhe: the proof of LAW log_ffi_malformed_unless_request
#
# Each decoder layer that answers Got gives the prefix of the encoding
# (wire_nat_exact) and a Nat that fits (wire_nat_decoded_fits); a Bad
# layer or an unknown Maybe tag answers the malformed error, which the
# premise refutes. The rest after the last newline is whatever is left.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits

def lmr.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def lmr.pair(+s: String, +x: String, +b: Bool, e1: {s == x : String}, e2: {b == True{} : Bool}) -> {(s, b) == (x, True{}) : String & Bool}:
  %Equal.sym(String, s, x, e1) : {(_, b) == (x, True{}) : String & Bool}
  %Equal.sym(Bool, b, True{}, e2) : {(x, _) == (x, True{}) : String & Bool}
  {==}

def lmr.G(+s: String) -> Type:
  &len: Nat -> &last: Maybe<&2, Nat> -> &rest: String -> {(s, Bool.and(LawsBase.wire_fits(len), Log.log_last_fits(last))) == (Log.log_spell_req_then(len, last, rest), True{}) : String & Bool}

# the length, then the last newline, then the rest
def lmr.fin(+s: String, +n: Nat, -s1: String, +m: Maybe<&2, Nat>, +s2: String, ex: {s == Wr.put_nat(n, s1) : String}, ex1: {s1 == Log.log_spell_last(m, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fm: {Log.log_last_fits(m) == True{} : Bool}) -> lmr.G(s):
  +e = Equal.trans(String, s, Wr.put_nat(n, s1), Wr.put_nat(n, Log.log_spell_last(m, s2)), ex, Equal.cong(String, String, z => Wr.put_nat(n, z), s1, Log.log_spell_last(m, s2), ex1))
  (n, (m, (s2, lmr.pair(s, Log.log_spell_req_then(n, m, s2), Bool.and(LawsBase.wire_fits(n), Log.log_last_fits(m)), e, lmr.and_tt(LawsBase.wire_fits(n), Log.log_last_fits(m), fn, fm)))))

def lmr.some(+s: String, +n: Nat, -s1: String, +s2: String, ex: {s == Wr.put_nat(n, s1) : String}, ex1: {s1 == Wr.put_nat(1n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, r: Wr.Dec<Nat>, er: {Wr.get_nat(s2) == r : Wr.Dec<Nat>}, other: {String.eq(FLg.ffi.go(FLg.get_req.last(n, FLg.get_last.some(r))), Wr.err("log: malformed request")) == False{} : Bool}) -> lmr.G(s):
  match r:
    case Wr.Got{+i, +s3}:
      +er2 = er
      +ex2 = Wire.wire_nat_exact(s2, i, s3, er2)
      lmr.fin(s, n, s1, Some{i}, s3, ex, (%ex2 : {s1 == Wr.put_nat(1n, _) : String}; ex1), fn, Wire.wire_nat_decoded_fits(s2, i, s3, er2))
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(lmr.G(s), other)

def lmr.tag(+s: String, +n: Nat, +s1: String, ex: {s == Wr.put_nat(n, s1) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, r: Wr.Dec<Nat>, er: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}, other: {String.eq(FLg.ffi.go(FLg.get_req.last(n, FLg.get_last.tag(r))), Wr.err("log: malformed request")) == False{} : Bool}) -> lmr.G(s):
  match r:
    case Wr.Got{+t, +s2}:
      match t:
        case 0n:
          lmr.fin(s, n, s1, None{}, s2, ex, Wire.wire_nat_exact(s1, 0n, s2, er), fn, {==})
        case 1n:
          lmr.some(s, n, s1, s2, ex, Wire.wire_nat_exact(s1, 1n, s2, er), fn, Wr.get_nat(s2), {==}, other)
        case 2n+k:
          LLogicLogic.pt.absurd(lmr.G(s), other)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(lmr.G(s), other)

def lmr.req(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}, other: {String.eq(FLg.ffi.go(FLg.get_req.len(r)), Wr.err("log: malformed request")) == False{} : Bool}) -> lmr.G(s):
  match r:
    case Wr.Got{+n, +s1}:
      +er2 = er
      lmr.tag(s, n, s1, Wire.wire_nat_exact(s, n, s1, er2), Wire.wire_nat_decoded_fits(s, n, s1, er2), Wr.get_nat(s1), {==}, other)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(lmr.G(s), other)

def Log.log_ffi_malformed_unless_request(s, other):
  lmr.req(s, Wr.get_nat(s), {==}, other)
