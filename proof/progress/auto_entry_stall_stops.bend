# eukhe: the proof of LAW auto_entry_stall_stops
# PROOF: the spelled request is the one auto_entry answers; the work's
# count did not grow and s is below t, so judge counts s + 1 stalls, and
# twice the cap is reached: Stop.

import Base
import ../../bend/ffi_progress.bend as FPr
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/progress.bend as Progress
import ../base/nat.bend as LNat
import ./base.bend as LA

def Progress.auto_entry_stall_stops(t, cap, s, w, work, h, same, below, reached):
  %LA.pe.answer(t, cap, Some{Pr.Prior{s, w}}, work, h) : {_ == Progress.gs_reply(1n, 1n+s) : String}
  %Equal.sym(Bool, Nat.is_lt(w, work), False{}, same) : {FPr.put_run(Pr.check(cap, Nat.min(s, Nat.sub(t, 1n)), _), "") == Progress.gs_reply(1n, 1n+s) : String}
  %LNat.pj.min_of_le(s, Nat.sub(t, 1n), LA.pp.lt_pred(s, t, below)) : {FPr.put_run(Pr.check(cap, _, False{}), "") == Progress.gs_reply(1n, 1n+s) : String}
  %Equal.sym(Bool, Nat.is_le(Nat.add(cap, cap), 1n+s), True{}, reached) : {FPr.put_run(Pr.strike.put(_, Nat.is_eq(cap, 1n+s), 1n+s), "") == Progress.gs_reply(1n, 1n+s) : String}
  {==}
