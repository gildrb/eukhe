# eukhe: the proof of LAW cvar_open_spelled
# The spec's spelling is the entry's encoding (LB.cve.put_table), which
# opens that table (cvar_ffi_open).

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar.bend as Cvar
import ../../laws/cvar_entry.bend as CvarEntry
import ./base.bend as LB
import ../cvar/cvar_ffi_open.bend as PFO

def CvarEntry.cvar_open_spelled(bs, as, h):
  %LB.cve.put_table(bs, as, "") : {FCv.open(_) == (FCv.Table{bs, as}, "") : FCv.St & String}
  Cvar.cvar_ffi_open(bs, as, h)
