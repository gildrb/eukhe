# eukhe: the proof of LAW cvar_ffi_exact
# The call reads as the spec reads (LB.cve.xreq) and answers the spec's
# expansion, spelled as the spec spells it (LB.cve.run).

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as Cvar
import ../../laws/cvar_entry.bend as CvarEntry
import ./base.bend as LB

def CvarEntry.cvar_ffi_exact(s):
  LB.cve.ffi(s)
