# eukhe: the proof of LAW replace_lt_single
#
# PROOF of LAW replace_lt_single: the order of [x] and [y] is the compare
# of x and y with nothing after them (rls.put).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace

def rls.put(c: Cmp) -> {Rp.lex.put(c, False{}) == Cmp.is_lt(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Replace.replace_lt_single(x, y):
  rls.put(Nat.cmp(x, y))
