# eukhe: the proof of LAW line_step_node_beyond_reply
# line.step reads the node only to ask whether the reply fits it: with
# both nodes at least the reply's bytes (its Text.len, LA.lp.len) the
# reply fits both and is the line, whole; every other branch never reads
# the node.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def lnb.says(f1: Bool, f2: Bool, -less: Bool, -p: Nat, -made: Nat, -n1: Nat, -n2: Nat, -b: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>, -ws: List<&2, C.W>, -len: Nat, e1: {f1 == True{} : Bool}, e2: {f2 == True{} : Bool}) -> {Compactor.spell_next(C.line.says(f1, less, p, made, n1, b, input, ws, len)) == Compactor.spell_next(C.line.says(f2, less, p, made, n2, b, input, ws, len)) : String}:
  match f1 f2:
    case True{} True{}:
      {==}
    case True{} False{}:
      LLogicLogic.pc.absurd_ft({Compactor.spell_next(C.line.says(True{}, less, p, made, n1, b, input, ws, len)) == Compactor.spell_next(C.line.says(False{}, less, p, made, n2, b, input, ws, len)) : String}, e2)
    case False{} y:
      LLogicLogic.pc.absurd_ft({Compactor.spell_next(C.line.says(False{}, less, p, made, n1, b, input, ws, len)) == Compactor.spell_next(C.line.says(y, less, p, made, n2, b, input, ws, len)) : String}, e1)

# a reply within the node fits it
def lnb.fit(+t: List<&2, C.W>, +n: Nat, e: {Nat.is_le(Compactor.bytes(t), n) == True{} : Bool}) -> {Nat.is_le(C.Text.len(t), n) == True{} : Bool}:
  %Equal.sym(Nat, C.Text.len(t), Compactor.bytes(t), LA.lp.len(t)) : {Nat.is_le(_, n) == True{} : Bool}
  e

def Compactor.line_step_node_beyond_reply(left, made, n1, n2, best, bl, input, r, le1, le2):
  match left:
    case 0n:
      {==}
    case 1n+p:
      match r:
        case C.Erred{}:
          {==}
        case C.Says{ws}:
          match ws:
            case Nil{}:
              {==}
            case +w <> +t:
              +len = C.Text.len(w <> t)
              lnb.says(Nat.is_le(len, n1), Nat.is_le(len, n2), C.shorter(len, best, bl), p, made, n1, n2, best, input, w <> t, len, lnb.fit(w <> t, n1, le1), lnb.fit(w <> t, n2, le2))
