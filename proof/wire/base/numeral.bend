# eukhe: lemmas of area wire: the laws' numerals (laws/wire.bend
# wire_numeral, wire_value, wire_numeral_chars) are the proofs' digit
# lists, lowest first (wn_okc, wo_value, wn_emit of proof/base/logic/).

import Base
import ../../../bend/wire.bend as Wr
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/logic/nat.bend as LLogicNat
import ../../base/logic/string.bend as LLogicString
import ../base.bend as LAWire
import ../wire_nat_exact.bend as PWireNatExact
import ./dec.bend as LWireDec

# both halves of an and hold
def wnm.and_tt(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# a digit by the table is below 10
def wnm.lt_is(d: Nat, h: {LLogicBool.wn_lt10(d) == True{} : Bool}) -> {Nat.is_lt(d, 10n) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+p:
      LLogicLogic.wn_absurd({Nat.is_lt(10n+p, 10n) == True{} : Bool}, h)

# below 10 is a digit by the table
def wnm.is_lt(+d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {LLogicBool.wn_lt10(d) == True{} : Bool}:
  Pair.snd({Chr{U32.from_nat(Nat.add(48n, d))} == Wr.dchar(d) : Char}, {LLogicBool.wn_lt10(d) == True{} : Bool}, PWireNatExact.wn_code(d, h))

# a highest digit by the table (not 0, below 10) is one by the laws' terms
def wnm.nz_hi(e: Nat, h: {LLogicBool.wn_nz10(e) == True{} : Bool}) -> {Bool.and(Nat.is_lt(0n, e), Nat.is_lt(e, 10n)) == True{} : Bool}:
  match e:
    case 0n:
      LLogicLogic.wn_absurd({Bool.and(Nat.is_lt(0n, 0n), Nat.is_lt(0n, 10n)) == True{} : Bool}, h)
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+p:
      LLogicLogic.wn_absurd({Bool.and(Nat.is_lt(0n, 10n+p), Nat.is_lt(10n+p, 10n)) == True{} : Bool}, h)

# and back
def wnm.hi_nz(e: Nat, h: {Bool.and(Nat.is_lt(0n, e), Nat.is_lt(e, 10n)) == True{} : Bool}) -> {LLogicBool.wn_nz10(e) == True{} : Bool}:
  match e:
    case 0n:
      LLogicLogic.wn_absurd({LLogicBool.wn_nz10(0n) == True{} : Bool}, h)
    case 1n++q:
      wnm.is_lt(1n+q, LLogicBool.wn_and_r(Nat.is_lt(0n, 1n+q), Nat.is_lt(1n+q, 10n), h))

# the table's canonical digits above the lowest are the laws' high part
def wnm.high(u: List<&2, Nat>, +e: Nat, +c: {LLogicBool.wn_okc(u, e) == True{} : Bool}) -> {Wire.wire_numeral.high(u, e) == True{} : Bool}:
  match u:
    case Nil{}:
      wnm.nz_hi(e, c)
    case Con{+f, +v}:
      wnm.and_tt(Nat.is_lt(e, 10n), Wire.wire_numeral.high(v, f),
        wnm.lt_is(e, LLogicBool.wn_and_l(LLogicBool.wn_lt10(e), LLogicBool.wn_okc(v, f), c)),
        wnm.high(v, f, LLogicBool.wn_and_r(LLogicBool.wn_lt10(e), LLogicBool.wn_okc(v, f), c)))

# and back
def wnm.okc(u: List<&2, Nat>, +e: Nat, +h: {Wire.wire_numeral.high(u, e) == True{} : Bool}) -> {LLogicBool.wn_okc(u, e) == True{} : Bool}:
  match u:
    case Nil{}:
      wnm.hi_nz(e, h)
    case Con{+f, +v}:
      wnm.and_tt(LLogicBool.wn_lt10(e), LLogicBool.wn_okc(v, f),
        wnm.is_lt(e, LLogicBool.wn_and_l(Nat.is_lt(e, 10n), Wire.wire_numeral.high(v, f), h)),
        wnm.okc(v, f, LLogicBool.wn_and_r(Nat.is_lt(e, 10n), Wire.wire_numeral.high(v, f), h)))

# a canonical digit list of the table is a numeral of the laws
def wnm.from(t: List<&2, Nat>, +d: Nat, +c: {LLogicBool.wn_okc(t, d) == True{} : Bool}) -> {Wire.wire_numeral.from(d, t) == True{} : Bool}:
  match t:
    case Nil{}:
      wnm.lt_is(d, LAWire.wn_nz_lt(d, c))
    case Con{+e, +u}:
      wnm.and_tt(Nat.is_lt(d, 10n), Wire.wire_numeral.high(u, e),
        wnm.lt_is(d, LLogicBool.wn_and_l(LLogicBool.wn_lt10(d), LLogicBool.wn_okc(u, e), c)),
        wnm.high(u, e, LLogicBool.wn_and_r(LLogicBool.wn_lt10(d), LLogicBool.wn_okc(u, e), c)))

# a numeral of the laws with two digits or more is canonical in the table
def wnm.okc_from(+d: Nat, +e: Nat, +u: List<&2, Nat>, +h: {Wire.wire_numeral.from(d, e <> u) == True{} : Bool}) -> {LLogicBool.wn_okc(e <> u, d) == True{} : Bool}:
  wnm.and_tt(LLogicBool.wn_lt10(d), LLogicBool.wn_okc(u, e),
    wnm.is_lt(d, LLogicBool.wn_and_l(Nat.is_lt(d, 10n), Wire.wire_numeral.high(u, e), h)),
    wnm.okc(u, e, LLogicBool.wn_and_r(Nat.is_lt(d, 10n), Wire.wire_numeral.high(u, e), h)))

# the laws' value is the table's
def wnm.value(ds: List<&2, Nat>) -> {Wire.wire_value(ds) == LLogicNat.wo_value(ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      Equal.cong(Nat, Nat, v => Nat.add(d, Nat.mul(10n, v)), Wire.wire_value(t), LLogicNat.wo_value(t), wnm.value(t))

# put_nat's emission of a canonical digit list is the laws' chars
def wnm.emit(t: List<&2, Nat>, +d: Nat, acc: String, +c: {LLogicBool.wn_okc(t, d) == True{} : Bool}) -> {LLogicString.wn_emit(d <> t, acc) == Wire.wire_numeral_chars(d <> t, acc) : String}:
  match t:
    case Nil{}:
      %LWireDec.wdec.char(d, LAWire.wn_nz_lt(d, c)) : {SCon{Wr.dchar(d), acc} == SCon{_, acc} : String}
      {==}
    case Con{+e, +u}:
      %LWireDec.wdec.char(d, LLogicBool.wn_and_l(LLogicBool.wn_lt10(d), LLogicBool.wn_okc(u, e), c)) : {LLogicString.wn_emit(e <> u, SCon{Wr.dchar(d), acc}) == Wire.wire_numeral_chars(e <> u, SCon{_, acc}) : String}
      wnm.emit(u, e, SCon{Wr.dchar(d), acc}, LLogicBool.wn_and_r(LLogicBool.wn_lt10(d), LLogicBool.wn_okc(u, e), c))
