# eukhe: the proof of LAW goal_new_act_counts
# PROOF: a < b is 1 + a <= b, and an act the session never did grows the
# work by at least one (LA.pp.new_work).

import Base
import ../../bend/ffi_progress.bend as FPr
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/progress.bend as Progress
import ../base/nat.bend as LNat
import ./base.bend as LA

def Progress.goal_new_act_counts(hist, seg, x, fresh, news):
  %Equal.sym(Bool, Nat.is_lt(Pr.work(hist), Pr.work(List.append(&2, Nat, hist, seg))), Nat.is_le(1n+Pr.work(hist), Pr.work(List.append(&2, Nat, hist, seg))), LA.pp.lt_is_le(Pr.work(hist), Pr.work(List.append(&2, Nat, hist, seg)))) : {_ == True{} : Bool}
  LA.pp.new_work(hist, seg, x, fresh, news)
