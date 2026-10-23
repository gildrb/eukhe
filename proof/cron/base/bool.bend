# eukhe: lemmas the proofs of area cron share: bool

import Base
import ./logic.bend as LALogic

# A recovery keeps the invariant
# ------------------------------

def pc.no_clear(b: Bool, +hd: Bool, live: {hd == False{} : Bool}) -> {Bool.or(Bool.and(b, Bool.not(Bool.or(b, False{}))), hd) == False{} : Bool}:
  match b:
    case True{}:
      live
    case False{}:
      live

# A pass that unwinds, or a process that dies, keeps the invariant
# ----------------------------------------------------------------

def pc.or_ff(a: Bool, +b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      LALogic.cron.pc.absurd({Bool.or(True{}, b) == False{} : Bool}, ha)
    case False{}:
      hb
