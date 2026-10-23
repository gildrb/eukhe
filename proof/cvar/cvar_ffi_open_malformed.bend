# eukhe: the proof of LAW cvar_ffi_open_malformed

import Base
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar.bend as Cvar

def Cvar.cvar_ffi_open_malformed(s, h):
  Equal.cong(Wr.Dec<FCv.St>, FCv.St & String, d => FCv.open.go(d), FCv.get_table(s), Wr.Bad{}, h)
