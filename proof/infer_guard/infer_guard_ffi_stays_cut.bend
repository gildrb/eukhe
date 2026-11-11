# eukhe: the proof of LAW infer_guard_ffi_stays_cut
#
# PROOF: the chunk that cuts moves the stepper as the model's feed
# (infer_guard_ffi_step) to the cut stream with its cut; a cut stream
# answers its cut to every input (gsc.ended, by induction on the inputs).

import Base
import ../../bend/infer_guard.bend as M
import ../../bend/ffi_infer_guard.bend as FG
import ../../laws/infer_guard.bend as InferGuard

# from a cut stream that answered o, every later step answers its cut
def gsc.ended(ins: List<&2, String>, +at: Nat, +p: Nat, o: String) -> {InferGuard.feed(ins, (FG.Ended{at, p}, o)) == o <> List.replicate(String, List.length(&2, String, ins), InferGuard.spell_cut(at, p)) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case i <> t:
      Equal.cong(List<&2, String>, List<&2, String>, z => o <> z, InferGuard.feed(t, (FG.Ended{at, p}, InferGuard.spell_cut(at, p))), InferGuard.spell_cut(at, p) <> List.replicate(String, List.length(&2, String, t), InferGuard.spell_cut(at, p)), gsc.ended(t, at, p, InferGuard.spell_cut(at, p)))

def InferGuard.infer_guard_ffi_stays_cut(g, x, at, p, ins, fits, cut):
  %Equal.sym(FG.St & String, FG.step(FG.Live{g}, InferGuard.spell_chunk(x)), InferGuard.spell_next(M.feed(g, x)), InferGuard.infer_guard_ffi_step(g, x, fits)) : {InferGuard.feed(ins, _) == List.replicate(String, 1n+List.length(&2, String, ins), InferGuard.spell_cut(at, p)) : List<&2, String>}
  %Equal.sym(M.Next, M.feed(g, x), M.Cuts{at, p}, cut) : {InferGuard.feed(ins, InferGuard.spell_next(_)) == List.replicate(String, 1n+List.length(&2, String, ins), InferGuard.spell_cut(at, p)) : List<&2, String>}
  gsc.ended(ins, at, p, InferGuard.spell_cut(at, p))
