# eukhe: the proof of LAW replace_lt_head_decides
#
# PROOF of LAW replace_lt_head_decides: split the compare of the first
# numbers (rlh.put): LT answers True; EQ and GT contradict x < y.

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../base/logic/logic.bend as LLogicLogic

def rlh.put(c: Cmp, -t: Bool, h: {Cmp.is_lt(c) == True{} : Bool}) -> {Rp.lex.put(c, t) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      LLogicLogic.supervisor.ps.absurdF({Rp.lex.put(EQ{}, t) == True{} : Bool}, h)
    case GT{}:
      LLogicLogic.supervisor.ps.absurdF({Rp.lex.put(GT{}, t) == True{} : Bool}, h)

def Replace.replace_lt_head_decides(x, y, xs, ys, less):
  rlh.put(Nat.cmp(x, y), Rp.lt(xs, ys), less)
