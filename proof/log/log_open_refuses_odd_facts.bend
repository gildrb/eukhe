# eukhe: the proof of LAW log_open_refuses_odd_facts
#
# The newline at i lies inside a file of len bytes exactly when 1 + i <=
# len, that is i < len (pl.le_succ_lt).

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log

def pl.le_succ_lt(i: Nat, n: Nat) -> {Nat.is_lt(i, n) == Nat.is_le(1n+i, n) : Bool}:
  match i n:
    case 0n 0n:
      {==}
    case 0n 1n+m:
      match m:
        case 0n:
          {==}
        case 1n+k:
          {==}
    case 1n+j 0n:
      {==}
    case 1n+j 1n+m:
      pl.le_succ_lt(j, m)

def Log.log_open_refuses_odd_facts(len, i, past):
  %pl.le_succ_lt(i, len) : {Lr.tail.in(_, len, 1n+i) == Lr.Odd{} : Lr.Tail}
  %Equal.sym(Bool, Nat.is_lt(i, len), False{}, past) : {Lr.tail.in(_, len, 1n+i) == Lr.Odd{} : Lr.Tail}
  {==}
