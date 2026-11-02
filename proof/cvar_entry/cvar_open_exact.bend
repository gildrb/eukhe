# eukhe: the proof of LAW cvar_open_exact
# An open reads the table as the spec reads it (LB.cve.table).

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar.bend as Cvar
import ../../laws/cvar_entry.bend as CvarEntry
import ./base.bend as LB

def CvarEntry.cvar_open_exact(s):
  LB.cve.open(s)
