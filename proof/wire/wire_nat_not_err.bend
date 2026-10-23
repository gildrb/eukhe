# eukhe: the proof of LAW wire_nat_not_err

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/list.bend as LList
import ../base/string.bend as LString
import ../base/wire.bend as LWire

# no digit char is 'E'
def wn_dchar_ne(d: Nat) -> {Char.is_eq(Wr.dchar(d), 'E') == False{} : Bool}:
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
      {==}

def wn_ne(ds: List<&2, Nat>, c: Char, t: String, hc: {Char.is_eq(c, 'E') == False{} : Bool})
  -> {LawsBase.wire_opens_err(LString.wn_emit(ds, SCon{c, t})) == False{} : Bool}:
  match ds:
    case Nil{}:
      hc
    case Con{+d, u}:
      wn_ne(u, Wr.dchar(d), SCon{c, t}, wn_dchar_ne(d))

def wn_not_err(+n: Nat, +rest: String) -> {LawsBase.wire_opens_err(Wr.put_nat(n, rest)) == False{} : Bool}:
  %Equal.sym(String, Wr.put_nat(n, rest), LString.wn_emit(LList.wn_full(n), SCon{',', rest}), LWire.wn_put_emit(n, rest)) : {LawsBase.wire_opens_err(_) == False{} : Bool}
  wn_ne(LList.wn_full(n), ',', rest, {==})

def Wire.wire_nat_not_err(n, rest):
  wn_not_err(n, rest)
