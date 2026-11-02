# eukhe: the proof of LAW forward_once
#
# PROOF of LAW forward_once: every seq the first pick hands on is at most
# its new cursor b (forward_all_new, forward_cursor_exact,
# wb_all_le_cursor); every seq the second pick hands on is past b
# (forward_all_new, wb_new_gt); so none is both (wb_disjoint).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker
import ./forward_all_new.bend as PWorkerForwardAllNew
import ./forward_cursor_exact.bend as PWorkerForwardCursorExact

def Worker.forward_once(c, ms, note, ms2, note2):
  +b = Worker.fw_cursor_of(Wk.pick(c, ms, note))
  +ps = Worker.fw_seqs(Worker.fw_new(c, ms))
  +qs = Worker.fw_seqs(Worker.fw_new(b, ms2))
  %Equal.sym(List<&2, Nat>, Worker.fw_picked_of(Wk.pick(c, ms, note)), ps, Worker.forward_all_new(c, ms, note)) : {Worker.fw_disjoint(_, Worker.fw_picked_of(Wk.pick(b, ms2, note2))) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, Worker.fw_picked_of(Wk.pick(b, ms2, note2)), qs, Worker.forward_all_new(b, ms2, note2)) : {Worker.fw_disjoint(ps, _) == True{} : Bool}
  LAWorker.wb_disjoint(ps, b, qs,
    Equal.trans(Bool, LAWorker.wb_all_le(ps, b), LAWorker.wb_all_le(ps, Worker.fw_cursor(ps, c)), True{},
      Equal.cong(Nat, Bool, z => LAWorker.wb_all_le(ps, z), b, Worker.fw_cursor(ps, c), Worker.forward_cursor_exact(c, ms, note)),
      LAWorker.wb_all_le_cursor(ps, c)),
    LAWorker.wb_new_gt(b, ms2))
