# eukhe: the proof of LAW goal_entry_stall_stops
# PROOF: the spelled request is the one goal_entry answers; the work's
# count did not grow and s is below t, so judge counts s + 1 stalls, and
# the cap decides Go or Stop.

import Base
import ../../bend/ffi_progress.bend as FPr
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/progress.bend as Progress
import ../base/nat.bend as LNat
import ./base.bend as LA

def Progress.goal_entry_stall_stops(t, cap, s, w, work, h, same, below, reached):
  %LA.pe.answer(t, cap, Some{Pr.Prior{s, w}}, work, h) : {_ == Progress.gs_reply(1n, 1n+s) : String}
  %Equal.sym(Bool, Nat.is_lt(w, work), False{}, same) : {FPr.put_goal(Pr.check(cap, Nat.min(s, Nat.sub(t, 1n)), _), "") == Progress.gs_reply(1n, 1n+s) : String}
  %LNat.pj.min_of_le(s, Nat.sub(t, 1n), LA.pp.lt_pred(s, t, below)) : {FPr.put_goal(Pr.check(cap, _, False{}), "") == Progress.gs_reply(1n, 1n+s) : String}
  %Equal.sym(Bool, Nat.is_le(cap, 1n+s), True{}, reached) : {FPr.put_goal(Pr.strike.put(_, 1n+s), "") == Progress.gs_reply(1n, 1n+s) : String}
  {==}
