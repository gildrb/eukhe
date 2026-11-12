# eukhe: the proof of LAW cvar_step_exact
# A step reads the key with the Nat reader, as the spec does, and answers
# the spec's press (bind_press_exact), spelled as the spec spells it.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as Cvar
import ../../laws/cvar_entry.bend as CvarEntry
import ./base.bend as LB

def CvarEntry.cvar_step_exact(bs, as, s):
  LB.cve.key_orig(bs, as, Wr.get_nat(s))
