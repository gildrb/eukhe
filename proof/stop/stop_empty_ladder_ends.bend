# eukhe: the proof of LAW stop_empty_ladder_ends
#
# PROOF: every note that is no empty note counts no empty note: the
# first empty reply gets note 1 and each next record computes notes 2, 3
# and the failed run; a row of 3 + x is not below 3 (x is 0 or more).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def se.ladder(+rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, other: {StopRecover.empty_note(k) == False{} : Bool}) -> {StopRecover.empty_helps(4n, rc, RnRecovery.Rec{k, row, same, last}) == [RnDecision.Redoes{1n}, RnDecision.Redoes{2n}, RnDecision.Redoes{3n}, RnDecision.Quits{}] : List<&2, RnDecision.Help>}:
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}
    case RnRecovery.Empties{}:
      LR.str.absurd_t({StopRecover.empty_helps(4n, rc, RnRecovery.Rec{RnRecovery.Empties{}, row, same, last}) == [RnDecision.Redoes{1n}, RnDecision.Redoes{2n}, RnDecision.Redoes{3n}, RnDecision.Quits{}] : List<&2, RnDecision.Help>}, other)

def se.past(+rc: RnRecovery.RCfg, +same: Nat, +last: Nat, +x: Nat) -> {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Empty{}, RnRecovery.Rec{RnRecovery.Empties{}, 3n+x, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}:
  match x:
    case 0n:
      {==}
    case 1n++y:
      {==}

def StopRecover.stop_empty_ladder_ends(rc, k, row, same, last, x, other):
  (se.ladder(rc, k, row, same, last, other), se.past(rc, same, last, x))
