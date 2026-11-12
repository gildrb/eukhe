# eukhe: the proof of LAW goal_entry_new_work
# PROOF: the spelled request is the one goal_entry answers; the work's
# count grew, so the check clears the count.

import Base
import ../../bend/ffi_progress.bend as FPr
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/progress.bend as Progress
import ../base/nat.bend as LNat
import ./base.bend as LA

def Progress.goal_entry_new_work(t, cap, s, w, work, h, grew):
  %LA.pe.answer(t, cap, Some{Pr.Prior{s, w}}, work, h) : {_ == Progress.gs_reply(0n, 0n) : String}
  %Equal.sym(Bool, Nat.is_lt(w, work), True{}, grew) : {FPr.put_goal(Pr.check(cap, Nat.min(s, Nat.sub(t, 1n)), _), "") == Progress.gs_reply(0n, 0n) : String}
  {==}
