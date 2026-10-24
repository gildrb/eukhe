# eukhe: the proof of LAW compactor_ffi_after
# The failures left read back (LWire.pw6.nat); the outcome's tag is a
# closed string; the entry's encoding of the model's Pend is the spec's.

import Base
import ../../bend/compactor.bend as C
import ../../bend/ffi_compactor.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/compactor.bend as Compactor
import ../base/wire.bend as LWire

# the entry writes a Pend as the spec does
def caf.pend(p: C.Pend) -> {FC.put_pend(p) == Compactor.spell_pend(p, "") : String}:
  match p:
    case C.Made{}:
      {==}
    case C.Owed{n}:
      {==}

def caf.owed(+n: Nat, o: C.Outcome, +fits: {LawsBase.wire_fits(n) == True{} : Bool}) -> {FC.ffi(Compactor.spell_after(C.Owed{n}, o)) == Compactor.spell_pend(C.Pend.after(C.Owed{n}, o), "") : String}:
  match o:
    case C.Built{}:
      %LWire.pw6.nat(n, Wr.put_nat(0n, ""), fits) : {FC.run(FC.get_after.owed(_)) == Compactor.spell_pend(C.Pend.after(C.Owed{n}, C.Built{}), "") : String}
      caf.pend(C.Pend.after(C.Owed{n}, C.Built{}))
    case C.Failed{}:
      %LWire.pw6.nat(n, Wr.put_nat(1n, ""), fits) : {FC.run(FC.get_after.owed(_)) == Compactor.spell_pend(C.Pend.after(C.Owed{n}, C.Failed{}), "") : String}
      caf.pend(C.Pend.after(C.Owed{n}, C.Failed{}))
    case C.Disk{}:
      %LWire.pw6.nat(n, Wr.put_nat(2n, ""), fits) : {FC.run(FC.get_after.owed(_)) == Compactor.spell_pend(C.Pend.after(C.Owed{n}, C.Disk{}), "") : String}
      caf.pend(C.Pend.after(C.Owed{n}, C.Disk{}))
    case C.Stopped{}:
      %LWire.pw6.nat(n, Wr.put_nat(3n, ""), fits) : {FC.run(FC.get_after.owed(_)) == Compactor.spell_pend(C.Pend.after(C.Owed{n}, C.Stopped{}), "") : String}
      caf.pend(C.Pend.after(C.Owed{n}, C.Stopped{}))

def Compactor.compactor_ffi_after(p, o, fits):
  match p:
    case C.Made{}:
      match o:
        case C.Built{}:
          {==}
        case C.Failed{}:
          {==}
        case C.Disk{}:
          {==}
        case C.Stopped{}:
          {==}
    case C.Owed{n}:
      caf.owed(n, o, fits)
