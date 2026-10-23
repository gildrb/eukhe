# eukhe: the proof of LAW wire_nat_not_err

import Base
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ../base.bend as L

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
  -> {Laws.wire_opens_err(L.wn_emit(ds, SCon{c, t})) == False{} : Bool}:
  match ds:
    case Nil{}:
      hc
    case Con{+d, u}:
      wn_ne(u, Wr.dchar(d), SCon{c, t}, wn_dchar_ne(d))

def wn_not_err(+n: Nat, +rest: String) -> {Laws.wire_opens_err(Wr.put_nat(n, rest)) == False{} : Bool}:
  %Equal.sym(String, Wr.put_nat(n, rest), L.wn_emit(L.wn_full(n), SCon{',', rest}), L.wn_put_emit(n, rest)) : {Laws.wire_opens_err(_) == False{} : Bool}
  wn_ne(L.wn_full(n), ',', rest, {==})

def Laws.wire_nat_not_err(n, rest):
  wn_not_err(n, rest)
