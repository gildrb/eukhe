# eukhe: the proof of LAW log_ffi_reads_only_fitting_requests
#
# As log_ffi_reads_only_requests: each decoder layer that answers Got gives
# the prefix of the encoding (wire_nat_exact), and every Nat it decoded
# fits the wire (wire_nat_decoded_fits); a Bad layer, an unknown tag or
# input left over answers the error form, which the premise refutes.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits

def pf.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def pf.G(s: String) -> Type:
  &len: Nat -> &last: Maybe<&2, Nat> -> ({s == Log.log_spell_req(len, last) : String} & {Bool.and(LawsBase.wire_fits(len), Log.log_last_fits(last)) == True{} : Bool})

def pf.lastq(s2: String, +s: String, +n: Nat, -s1: String, +m: Maybe<&2, Nat>, ex: {s == Wr.put_nat(n, s1) : String}, ex1: {s1 == Log.log_spell_last(m, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fm: {Log.log_last_fits(m) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FLg.ffi.end(Wr.end(s2), FLg.Req{n, m})) == False{} : Bool}) -> pf.G(s):
  match s2:
    case SNil{}:
      (n, (m, ((%ex1 : {s == Wr.put_nat(n, _) : String}; ex), pf.and_tt(LawsBase.wire_fits(n), Log.log_last_fits(m), fn, fm))))
    case SCon{c, t}:
      LLogicLogic.pt.absurd(pf.G(s), ok)

def pf.some(+s: String, +n: Nat, -s1: String, +s2: String, ex: {s == Wr.put_nat(n, s1) : String}, ex1: {s1 == Wr.put_nat(1n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, r: Wr.Dec<Nat>, er: {Wr.get_nat(s2) == r : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FLg.ffi.go(FLg.get_req.last(n, FLg.get_last.some(r)))) == False{} : Bool}) -> pf.G(s):
  match r:
    case Wr.Got{+i, +s3}:
      +er2 = er
      +ex2 = Wire.wire_nat_exact(s2, i, s3, er2)
      pf.lastq(s3, s, n, s1, Some{i}, ex, (%ex2 : {s1 == Wr.put_nat(1n, _) : String}; ex1), fn, Wire.wire_nat_decoded_fits(s2, i, s3, er2), ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(pf.G(s), ok)

def pf.tag(+s: String, +n: Nat, +s1: String, ex: {s == Wr.put_nat(n, s1) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, r: Wr.Dec<Nat>, er: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FLg.ffi.go(FLg.get_req.last(n, FLg.get_last.tag(r)))) == False{} : Bool}) -> pf.G(s):
  match r:
    case Wr.Got{+t, +s2}:
      match t:
        case 0n:
          pf.lastq(s2, s, n, s1, None{}, ex, Wire.wire_nat_exact(s1, 0n, s2, er), fn, {==}, ok)
        case 1n:
          pf.some(s, n, s1, s2, ex, Wire.wire_nat_exact(s1, 1n, s2, er), fn, Wr.get_nat(s2), {==}, ok)
        case 2n+k:
          LLogicLogic.pt.absurd(pf.G(s), ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(pf.G(s), ok)

def pf.req(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FLg.ffi.go(FLg.get_req.len(r))) == False{} : Bool}) -> pf.G(s):
  match r:
    case Wr.Got{+n, +s1}:
      +er2 = er
      pf.tag(s, n, s1, Wire.wire_nat_exact(s, n, s1, er2), Wire.wire_nat_decoded_fits(s, n, s1, er2), Wr.get_nat(s1), {==}, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(pf.G(s), ok)

def Log.log_ffi_reads_only_fitting_requests(s, ok):
  pf.req(s, Wr.get_nat(s), {==}, ok)
