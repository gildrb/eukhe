# eukhe: the proof of LAW facts_bedrock_effort_oracle

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat

# Oracles
# -------

# a native-xhigh model whose map keeps the promise sends xhigh at xhigh
def pf.xhigh(+m: Fx.EMap, ok: {Fx.native_ok.e(Fx.EMap.at(m, Fx.EXhigh{})) == True{} : Bool}) -> {5n == Fx.effort(m, Fx.EXhigh{}) : Nat}:
  match m:
    case Fx.EMap{mi, lo, me, hi, xh, mx}:
      match xh:
        case None{}:
          LLogicLogic.pq.absurdF({5n == Fx.effort.default(Fx.EXhigh{}) : Nat}, ok)
        case Some{w}:
          match w:
            case None{}:
              LLogicLogic.pq.absurdF({5n == Fx.effort.default(Fx.EXhigh{}) : Nat}, ok)
            case Some{v}:
              Equal.sym(Nat, v, 5n, LLogicNat.pq.eq_true(v, 5n, ok))

def pf.facts_bedrock_effort_oracle(native: Bool, +m: Fx.EMap, +l: Fx.ELv, ok: {Fx.native_ok(native, m) == True{} : Bool}) -> {Fx.effort.old(native, m, l) == Fx.effort(m, l) : Nat}:
  match native:
    case False{}:
      {==}
    case True{}:
      match l:
        case Fx.EMinimal{}:
          {==}
        case Fx.ELow{}:
          {==}
        case Fx.EMedium{}:
          {==}
        case Fx.EHigh{}:
          {==}
        case Fx.EMax{}:
          {==}
        case Fx.EXhigh{}:
          pf.xhigh(m, ok)

def Facts.facts_bedrock_effort_oracle(native, m, l, ok):
  pf.facts_bedrock_effort_oracle(native, m, l, ok)
