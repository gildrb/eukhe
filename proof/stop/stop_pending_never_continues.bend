# eukhe: the proof of LAW stop_pending_never_continues
#
# PROOF: the walk is the spec's (LA.stb.walk), whose picks are never PendingWork's, case by case.

import Base
import ../../bend/stop.bend as S
import ../../spec/harness/stop.bend as StSpec
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def pends.ann(a: Bool, p: Bool) -> {Stop.pends(StSpec.announced(a, p)) == False{} : Bool}:
  match a p:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def pends.pick(f: S.Facts) -> {Stop.pends(StSpec.pick(f)) == False{} : Bool}:
  match f:
    case S.Facts{c, t, b, p, +s}:
      match c:
        case True{}:
          {==}
        case False{}:
          match t:
            case False{}:
              {==}
            case True{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  match p:
                    case True{}:
                      {==}
                    case False{}:
                      pends.ann(StSpec.asks(s), StSpec.promises(s))

def Stop.stop_pending_never_continues(f):
  %Equal.sym(S.Pick, S.walk(f), StSpec.pick(f), LA.stb.walk(f)) : {Stop.pends(_) == False{} : Bool}
  pends.pick(f)
