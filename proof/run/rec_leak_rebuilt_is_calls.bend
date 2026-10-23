# eukhe: the proof of LAW rec_leak_rebuilt_is_calls

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def leak_rebuilt_is_calls(+rc: Rn.RCfg, +h: Nat, kept: Bool, r: Rn.Rec) -> {Rn.Rec.step(rc, Rn.Leak{True{}, h, kept}, r) == Rn.Rec.step(rc, Rn.Ran{h, kept}, r) : Rn.Dec}:
  match r:
    case Rn.Rec{k, row, same, last}:
      {==}

def Run.rec_leak_rebuilt_is_calls(rc, h, kept, r):
  leak_rebuilt_is_calls(rc, h, kept, r)
