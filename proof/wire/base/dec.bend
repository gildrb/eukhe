# eukhe: lemmas of area wire: the encoders of bend/wire.bend write the
# laws-side spellers of laws/base.bend (wire_dec: decimal by division,
# wire_bool_char: T or F), which the spec of laws/wire_entry.bend and
# wire_list_spells_items spell with, and the readers read them back. They
# are lemmas, not laws: the requirement of the spelling is LAW
# wire_nat_spells_digits.

import Base
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/pair.bend as LPair

# a digit's char in put_nat's table is the char of its code
def wdec.char(d: Nat, h: {LLogicBool.wn_lt10(d) == True{} : Bool}) -> {Wr.dchar(d) == LawsBase.wire_dec_char(d) : Char}:
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
      LLogicLogic.cb_absurd({Wr.dchar(10n+p) == LawsBase.wire_dec_char(10n+p) : Char}, h)

# the lowest digit of m
def wdec.low(+m: Nat) -> {Wr.dchar(Nat.mod(m, 10n)) == LawsBase.wire_dec_char(Nat.mod(m, 10n)) : Char}:
  wdec.char(Nat.mod(m, 10n), LPair.wn_mod_lt(m))

# the division loops agree
def wdec.go(g: Nat, n: Nat, acc: String) -> {Wr.put_nat.go(g, n, acc) == LawsBase.wire_dec.go(g, n, acc) : String}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      match n:
        case 0n:
          {==}
        case 1n+p:
          +m = {1n+p : Nat}
          %wdec.low(m) : {Wr.put_nat.go(f, Nat.div(m, 10n), SCon{Wr.dchar(Nat.mod(m, 10n)), acc}) == LawsBase.wire_dec.go(f, Nat.div(m, 10n), SCon{_, acc}) : String}
          wdec.go(f, Nat.div(m, 10n), SCon{Wr.dchar(Nat.mod(m, 10n)), acc})

# put_nat writes wire_dec
def wdec.nat(+n: Nat, rest: String) -> {Wr.put_nat(n, rest) == LawsBase.wire_dec(n, rest) : String}:
  %wdec.low(n) : {Wr.put_nat(n, rest) == LawsBase.wire_dec.go(n, Nat.div(n, 10n), SCon{_, SCon{',', rest}}) : String}
  wdec.go(n, Nat.div(n, 10n), SCon{Wr.dchar(Nat.mod(n, 10n)), SCon{',', rest}})

# put_u32 writes wire_dec of the value
def wdec.u32(+x: U32, rest: String) -> {Wr.put_u32(x, rest) == LawsBase.wire_dec(U32.to_nat(x), rest) : String}:
  wdec.nat(U32.to_nat(x), rest)

# put_bool writes wire_bool_char
def wdec.bool(b: Bool, rest: String) -> {Wr.put_bool(b, rest) == SCon{LawsBase.wire_bool_char(b), rest} : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the Nat reader reads wire_dec of a Nat that fits
def wdec.reads_nat(+n: Nat, rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.get_nat(LawsBase.wire_dec(n, rest)) == Wr.Got{n, rest} : Wr.Dec<Nat>}:
  +r = rest
  %wdec.nat(n, r) : {Wr.get_nat(_) == Wr.Got{n, r} : Wr.Dec<Nat>}
  Wire.wire_nat_round_trip(n, r, h)

# the Bool reader reads wire_bool_char
def wdec.reads_bool(b: Bool, rest: String) -> {Wr.get_bool(SCon{LawsBase.wire_bool_char(b), rest}) == Wr.Got{b, rest} : Wr.Dec<Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
