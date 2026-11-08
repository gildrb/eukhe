# eukhe: the proof of LAW infer_guard_ffi_step_spec
# A guard reads the chunk as the laws' reader does, stage by stage; a
# whole chunk gets the model's feed, which is the spec's
# (infer_guard_feed_exact), written as the spec writes it (gfs.of); a cut
# stream and a refused open answer as the spec says by computation.

import Base
import ../../bend/infer_guard.bend as M
import ../../bend/ffi_infer_guard.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/infer_guard.bend as InferGuard
import ./infer_guard_ffi_step.bend as PGfs
import ./infer_guard_feed_exact.bend as PGfe

def gss.end(b: Bool, +g: M.St, +x: Nat) -> {FG.step.end(b, g, x) == InferGuard.step_spec.chunk(g, InferGuard.read_nat.end(b, x)) : FG.St & String}:
  match b:
    case True{}:
      %InferGuard.infer_guard_feed_exact(g, x) : {FG.step.of(M.feed(g, x)) == InferGuard.spell_next(_) : FG.St & String}
      PGfs.gfs.of(M.feed(g, x))
    case False{}:
      {==}

def gss.chunk(+g: M.St, d: Wr.Dec<Nat>) -> {FG.step.chunk(g, d) == InferGuard.step_spec.chunk(g, InferGuard.read_nat.whole(d)) : FG.St & String}:
  match d:
    case Wr.Got{x, s}:
      gss.end(Wr.end(s), g, x)
    case Wr.Bad{}:
      {==}

def InferGuard.infer_guard_ffi_step_spec(st, s):
  match st:
    case FG.Live{g}:
      gss.chunk(g, Wr.get_nat(s))
    case FG.Ended{at, p}:
      {==}
    case FG.Shut{}:
      {==}
