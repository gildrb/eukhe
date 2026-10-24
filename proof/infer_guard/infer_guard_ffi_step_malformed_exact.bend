# eukhe: the proof of LAW infer_guard_ffi_step_malformed_exact
# The laws' reader reads the chunk as the entry does; where it finds no
# whole Nat, the entry found none either and keeps the guard.

import Base
import ../../bend/infer_guard.bend as M
import ../../bend/ffi_infer_guard.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/infer_guard.bend as InferGuard
import ../base/wire.bend as LWire

def gsm.if_none(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def gsm.absurd(-G: Type, -k: Nat, e: {Some{k} == None{} : Maybe<&2, Nat>}) -> G:
  %e : gsm.if_none(_, G)
  Unit{}

def gsm.end(b: Bool, -g: M.St, -x: Nat, no: {InferGuard.read_nat.end(b, x) == None{} : Maybe<&2, Nat>}) -> {FG.step.end(b, g, x) == (FG.Live{g}, SCon{'E', SCon{' ', "infer_guard: malformed chunk"}}) : FG.St & String}:
  match b:
    case True{}:
      gsm.absurd({FG.step.end(True{}, g, x) == (FG.Live{g}, SCon{'E', SCon{' ', "infer_guard: malformed chunk"}}) : FG.St & String}, x, no)
    case False{}:
      {==}

def gsm.go(-g: M.St, d: Wr.Dec<Nat>, no: {InferGuard.read_nat.whole(d) == None{} : Maybe<&2, Nat>}) -> {FG.step.chunk(g, d) == (FG.Live{g}, SCon{'E', SCon{' ', "infer_guard: malformed chunk"}}) : FG.St & String}:
  match d:
    case Wr.Got{x, s}:
      gsm.end(Wr.end(s), g, x, no)
    case Wr.Bad{}:
      {==}

def InferGuard.infer_guard_ffi_step_malformed_exact(g, s, no):
  gsm.go(g, Wr.get_nat(s), no)
