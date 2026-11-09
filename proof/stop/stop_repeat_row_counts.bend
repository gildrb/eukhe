# eukhe: the proof of LAW stop_repeat_row_counts
#
# PROOF: the first round starts a row of 1 (LR.str.rep_start); each further kept round below the cap grows it by one (LR.str.rep_go, by induction).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_repeat_row_counts(rc, h, n, fresh):
  match rc:
    case RnRecovery.RCfg{l, le, re, rp}:
      match n:
        case 0n:
          {==}
        case 1n++q:
          +b = LR.str.lt_below(1n+q, rp, fresh)
          +prem = LR.str.below_move(1n+q, 1n+Nat.add(q, 0n), rp, Equal.cong(Nat, Nat, z => 1n+z, q, Nat.add(q, 0n), Equal.sym(Nat, Nat.add(q, 0n), q, LR.str.add_zero(q))), b)
          %Equal.sym(RnRecovery.Dec, RnRecovery.Rec.step(RnRecovery.RCfg{l, le, re, rp}, RnRecovery.Ran{h, True{}}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 0n, 0n}), RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n, h}}, LR.str.rep_start(h, l, le, re, rp, LR.str.below_one(q, rp, b))) : {RnRecovery.Rec.same(RnRecovery.Rec.go(StopRecover.kept_rounds(q, h), RnRecovery.RCfg{l, le, re, rp}, RnRecovery.Dec.r(_))) == 1n+q : Nat}
          %Equal.sym(RnRecovery.Rec, RnRecovery.Rec.go(StopRecover.kept_rounds(q, h), RnRecovery.RCfg{l, le, re, rp}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n+0n, h}), RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n+Nat.add(q, 0n), h}, LR.str.rep_go(q, 0n, h, l, le, re, rp, prem)) : {RnRecovery.Rec.same(_) == 1n+q : Nat}
          %Equal.sym(Nat, Nat.add(q, 0n), q, LR.str.add_zero(q)) : {1n+_ == 1n+q : Nat}
          {==}
