# eukhe: the proof of LAW forward_picks_split
#
# PROOF of LAW forward_picks_split: the pick hands on the seqs of the
# model's messages past the cursor; those of ms ++ ns are those of ms, then
# those of ns (wb_after_app), and so are their seqs (wb_seqs_app); the note
# never reaches them.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker/forward.bend as WorkerForward
import ./base.bend as LAWorker

def WorkerForward.forward_picks_split(c, ms, ns, note):
  %Equal.sym(List<&2, Wk.UMsg>, Wk.after(c, List.append(&2, Wk.UMsg, ms, ns)), List.append(&2, Wk.UMsg, Wk.after(c, ms), Wk.after(c, ns)), LAWorker.wb_after_app(c, ms, ns)) : {Wk.seqs(_) == List.append(&2, Nat, Wk.seqs(Wk.after(c, ms)), Wk.seqs(Wk.after(c, ns))) : List<&2, Nat>}
  LAWorker.wb_seqs_app(Wk.after(c, ms), Wk.after(c, ns))
