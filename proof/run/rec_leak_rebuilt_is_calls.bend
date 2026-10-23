# eukhe: the proof of LAW rec_leak_rebuilt_is_calls

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run

def leak_rebuilt_is_calls(+rc: RnRecovery.RCfg, +h: Nat, kept: Bool, r: RnRecovery.Rec) -> {RnRecovery.Rec.step(rc, RnRecovery.Leak{True{}, h, kept}, r) == RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, r) : RnRecovery.Dec}:
  match r:
    case RnRecovery.Rec{k, row, same, last}:
      {==}

def Run.rec_leak_rebuilt_is_calls(rc, h, kept, r):
  leak_rebuilt_is_calls(rc, h, kept, r)
