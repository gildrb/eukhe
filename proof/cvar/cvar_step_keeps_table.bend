# eukhe: the proof of LAW cvar_step_keeps_table
#
# PROOF: every arm of the press (a key read whole, input left over, a
# malformed key) answers with the table it was given.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry

def ckt.go(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, d: Wr.Dec<Nat>) -> {CvarEntry.cvar_st_of(FCv.step.key(bs, as, d)) == FCv.Table{bs, as} : FCv.St}:
  match d:
    case Wr.Got{k, r}:
      match r:
        case SNil{}:
          {==}
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def CvarEntry.cvar_step_keeps_table(bs, as, s):
  ckt.go(bs, as, Wr.get_nat(s))
