# eukhe: the proof of LAW rec_run_steps_each_reply
#
# PROOF: Rec.run of no reply is the start; one more reply at the end is
# one more step, by induction on the replies before it (rrun.go).

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover

def rrun.go(os: List<&2, RnRecovery.Out>, +rc: RnRecovery.RCfg, +o: RnRecovery.Out, r: RnRecovery.Rec) -> {RnRecovery.Rec.go(List.append(&2, RnRecovery.Out, os, o <> Nil{}), rc, r) == RnRecovery.Dec.r(RnRecovery.Rec.step(rc, o, RnRecovery.Rec.go(os, rc, r))) : RnRecovery.Rec}:
  match os:
    case Nil{}:
      {==}
    case +x <> rest:
      rrun.go(rest, rc, o, RnRecovery.Dec.r(RnRecovery.Rec.step(rc, x, r)))

def RunRecover.rec_run_steps_each_reply(rc, os, o):
  ({==}, rrun.go(os, rc, o, RnRecovery.Rec.init()))
