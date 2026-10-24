# eukhe: the proof of LAW compactor_ffi_open
# The tries read back (LWire.pw6.nat); then line.open decides on the tries
# alone (the node and the input stay in Rust): no tries ends with the
# input cut, any other count asks.

import Base
import ../../bend/compactor.bend as C
import ../../bend/ffi_compactor.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/compactor.bend as Compactor
import ../base/wire.bend as LWire

def cop.tries(t: Nat, -node: Nat, -input: List<&2, C.W>) -> {FC.put_next(C.line.open(t, 0n, Nil{})) == Compactor.spell_next(C.line.open(t, node, input)) : String}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

def Compactor.compactor_ffi_open(t, node, input, fits):
  %LWire.pw6.nat(t, "", fits) : {FC.run(FC.get_open(_)) == Compactor.spell_next(C.line.open(t, node, input)) : String}
  cop.tries(t, node, input)
