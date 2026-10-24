# eukhe: the proof of LAW wire_nat_decimal
#
# PROOF of LAW wire_nat_decimal: put_nat and wire_dec run the same
# division loop; each digit is a remainder below 10 (wn_mod_lt), whose
# char in put_nat's table is the char of code 48 + the digit (wd_char).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/pair.bend as LPair

# a digit's char in the table is the char of its code
def wd_char(d: Nat, h: {LLogicBool.wn_lt10(d) == True{} : Bool}) -> {Wr.dchar(d) == LawsBase.wire_dec_char(d) : Char}:
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
def wd_low(+m: Nat) -> {Wr.dchar(Nat.mod(m, 10n)) == LawsBase.wire_dec_char(Nat.mod(m, 10n)) : Char}:
  wd_char(Nat.mod(m, 10n), LPair.wn_mod_lt(m))

# the loops agree
def wd_go(g: Nat, n: Nat, acc: String) -> {Wr.put_nat.go(g, n, acc) == LawsBase.wire_dec.go(g, n, acc) : String}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      match n:
        case 0n:
          {==}
        case 1n+p:
          +m = {1n+p : Nat}
          %wd_low(m) : {Wr.put_nat.go(f, Nat.div(m, 10n), SCon{Wr.dchar(Nat.mod(m, 10n)), acc}) == LawsBase.wire_dec.go(f, Nat.div(m, 10n), SCon{_, acc}) : String}
          wd_go(f, Nat.div(m, 10n), SCon{Wr.dchar(Nat.mod(m, 10n)), acc})

def Wire.wire_nat_decimal(n, rest):
  %wd_low(n) : {Wr.put_nat(n, rest) == LawsBase.wire_dec.go(n, Nat.div(n, 10n), SCon{_, SCon{',', rest}}) : String}
  wd_go(n, Nat.div(n, 10n), SCon{Wr.dchar(Nat.mod(n, 10n)), SCon{',', rest}})
