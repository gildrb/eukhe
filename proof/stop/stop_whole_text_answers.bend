# eukhe: the proof of LAW stop_whole_text_answers
#
# PROOF: pending by pending, the walk lets the stop stand and the reply's text reads it as Plain.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/state.bend as RnState
import ../../bend/stop.bend as S
import ../../laws/stop.bend as Stop

def stp.whole_text_answers(p: Bool, sp: Bool, cu: Bool, +rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +w: Nat, +ca: Nat, +pr: Nat, +o: Nat, +wc: Bool, +lo: Bool) -> {S.walk(S.Facts{False{}, True{}, False{}, p, sp, cu}) == S.Stands{} : S.Pick} & {Stop.stop_reply(S.walk(S.Facts{False{}, True{}, False{}, p, sp, cu}), S.Facts{False{}, True{}, False{}, p, sp, cu}, rc, k, row, w, ca, pr, o, wc, lo) == RnState.Plain{} : RnState.Reply}:
  match p:
    case True{}:
      ({==}, {==})
    case False{}:
      ({==}, {==})

def Stop.stop_whole_text_answers(p, sp, cu, rc, k, row, w, ca, pr, o, wc, lo):
  stp.whole_text_answers(p, sp, cu, rc, k, row, w, ca, pr, o, wc, lo)
