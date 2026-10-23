# eukhe: the proof of LAW cvar_ffi_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_cvar.bend as FCv
import ../../LAWS.bend as Laws

def Laws.cvar_ffi_malformed(s, h):
  Equal.cong(Wr.Dec<FCv.Xreq>, String, d => FCv.ffi.go(d), FCv.get_xreq(s), Wr.Bad{}, h)
