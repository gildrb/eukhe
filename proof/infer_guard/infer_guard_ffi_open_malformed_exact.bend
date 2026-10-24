# eukhe: the proof of LAW infer_guard_ffi_open_malformed_exact
# The laws' reader reads the window as the entry does; where it finds no
# whole Nat, the entry found none either.

import Base
import ../../bend/infer_guard.bend as M
import ../../bend/ffi_infer_guard.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/infer_guard.bend as InferGuard
import ../base/wire.bend as LWire

def gom.if_none(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def gom.absurd(-G: Type, -k: Nat, e: {Some{k} == None{} : Maybe<&2, Nat>}) -> G:
  %e : gom.if_none(_, G)
  Unit{}

def gom.end(b: Bool, -k: Nat, no: {InferGuard.read_nat.end(b, k) == None{} : Maybe<&2, Nat>}) -> {FG.open.end(b, k) == (FG.Shut{}, SCon{'E', SCon{' ', "infer_guard: malformed window"}}) : FG.St & String}:
  match b:
    case True{}:
      gom.absurd({FG.open.end(True{}, k) == (FG.Shut{}, SCon{'E', SCon{' ', "infer_guard: malformed window"}}) : FG.St & String}, k, no)
    case False{}:
      {==}

def gom.go(d: Wr.Dec<Nat>, no: {InferGuard.read_nat.whole(d) == None{} : Maybe<&2, Nat>}) -> {FG.open.go(d) == (FG.Shut{}, SCon{'E', SCon{' ', "infer_guard: malformed window"}}) : FG.St & String}:
  match d:
    case Wr.Got{k, s}:
      gom.end(Wr.end(s), k, no)
    case Wr.Bad{}:
      {==}

def InferGuard.infer_guard_ffi_open_malformed_exact(s, no):
  gom.go(Wr.get_nat(s), no)
