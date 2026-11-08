# eukhe: the proof of LAW infer_guard_ffi_open_spec
# The open reads the window as the laws' reader does, stage by stage: a
# whole Nat opens a fresh guard, anything else the refused state.

import Base
import ../../bend/infer_guard.bend as M
import ../../bend/ffi_infer_guard.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/infer_guard.bend as InferGuard

def gos.end(b: Bool, k: Nat) -> {FG.open.end(b, k) == InferGuard.open_spec.of(InferGuard.read_nat.end(b, k)) : FG.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gos.go(d: Wr.Dec<Nat>) -> {FG.open.go(d) == InferGuard.open_spec.of(InferGuard.read_nat.whole(d)) : FG.St & String}:
  match d:
    case Wr.Got{k, s}:
      gos.end(Wr.end(s), k)
    case Wr.Bad{}:
      {==}

def InferGuard.infer_guard_ffi_open_spec(s):
  gos.go(Wr.get_nat(s))
