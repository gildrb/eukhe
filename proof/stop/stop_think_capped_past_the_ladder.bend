# eukhe: the proof of LAW stop_think_capped_past_the_ladder
#
# PROOF: a row of long + 1 + x is neither below long nor equal to it (by induction on long), so the ladder has no note left and quits.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

# a row past j + x is not below j
def ptl.not_below(+j: Nat, +x: Nat) -> {RnRecovery.below(1n+Nat.add(j, x), j) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n++i:
      ptl.not_below(i, x)

# a row past j + x is not j
def ptl.not_eq(+j: Nat, +x: Nat) -> {Nat.is_eq(1n+Nat.add(j, x), j) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n++i:
      ptl.not_eq(i, x)

def StopRecover.stop_think_capped_past_the_ladder(rc, w, c, p, o, lower, x):
  match rc:
    case RnRecovery.RCfg{j, le, re, rp}:
      match lower:
        case True{}:
          %Equal.sym(Bool, RnRecovery.below(1n+Nat.add(j, x), j), False{}, ptl.not_below(j, x)) : {RnDecision.Help.of(RnRecovery.rec.think.note(_, Bool.and(True{}, Nat.is_eq(1n+Nat.add(j, x), j)), 1n+Nat.add(j, x), 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, 1n+Nat.add(j, x), 0n, 0n})) == RnDecision.Quits{} : RnDecision.Help}
          %Equal.sym(Bool, Nat.is_eq(1n+Nat.add(j, x), j), False{}, ptl.not_eq(j, x)) : {RnDecision.Help.of(RnRecovery.rec.think.note(False{}, Bool.and(True{}, _), 1n+Nat.add(j, x), 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, 1n+Nat.add(j, x), 0n, 0n})) == RnDecision.Quits{} : RnDecision.Help}
          {==}
        case False{}:
          %Equal.sym(Bool, RnRecovery.below(1n+Nat.add(j, x), j), False{}, ptl.not_below(j, x)) : {RnDecision.Help.of(RnRecovery.rec.think.note(_, Bool.and(False{}, Nat.is_eq(1n+Nat.add(j, x), j)), 1n+Nat.add(j, x), 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, 1n+Nat.add(j, x), 0n, 0n})) == RnDecision.Quits{} : RnDecision.Help}
          {==}
