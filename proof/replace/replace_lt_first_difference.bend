# eukhe: the proof of LAW replace_lt_first_difference
#
# PROOF of LAW replace_lt_first_difference: by induction on the shared
# prefix (rlf.go): each shared number compares equal to itself and passes
# the question to the rest (LAReplace.pr.lex_same); at the first
# difference, x < y answers True (rlf.put).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LAReplace

def rlf.put(c: Cmp, -t: Bool, h: {Cmp.is_lt(c) == True{} : Bool}) -> {Rp.lex.put(c, t) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      LLogicLogic.supervisor.ps.absurdF({Rp.lex.put(EQ{}, t) == True{} : Bool}, h)
    case GT{}:
      LLogicLogic.supervisor.ps.absurdF({Rp.lex.put(GT{}, t) == True{} : Bool}, h)

def rlf.go(p: List<&2, Nat>, x: Nat, y: Nat, -xr: List<&2, Nat>, -yr: List<&2, Nat>, less: {Nat.is_lt(x, y) == True{} : Bool}) -> {Rp.lt(List.append(&2, Nat, p, x <> xr), List.append(&2, Nat, p, y <> yr)) == True{} : Bool}:
  match p:
    case Nil{}:
      rlf.put(Nat.cmp(x, y), Rp.lt(xr, yr), less)
    case +q <> +pr:
      Equal.trans(Bool, Rp.lex(q, q, Rp.lt(List.append(&2, Nat, pr, x <> xr), List.append(&2, Nat, pr, y <> yr))), Rp.lt(List.append(&2, Nat, pr, x <> xr), List.append(&2, Nat, pr, y <> yr)), True{}, LAReplace.pr.lex_same(q, Rp.lt(List.append(&2, Nat, pr, x <> xr), List.append(&2, Nat, pr, y <> yr))), rlf.go(pr, x, y, xr, yr, less))

def Replace.replace_lt_first_difference(p, x, y, xr, yr, less):
  rlf.go(p, x, y, xr, yr, less)
