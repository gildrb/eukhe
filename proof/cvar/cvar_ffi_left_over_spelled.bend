# eukhe: the proof of LAW cvar_ffi_left_over_spelled
#
# PROOF: the spelled request is the entry's own encoding (cvs.xreq), which
# reads back with the rest untouched (LA.pvf.xreq_rt); the rest is not
# empty, so the entry answers the left-over error.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ./base.bend as LA
import ./base/spell.bend as LS

def CvarEntry.cvar_ffi_left_over_spelled(as, cs, fits, c, t):
  %LS.cvs.xreq(as, cs, SCon{c, t}) : {FCv.ffi(_) == Wr.err("cvar: input left over") : String}
  Equal.cong(Wr.Dec<FCv.Xreq>, String, d => FCv.ffi.go(d), FCv.get_xreq(FCv.put_xreq(FCv.Xreq{as, cs}, SCon{c, t})), Wr.Got{FCv.Xreq{as, cs}, SCon{c, t}}, LA.pvf.xreq_rt(as, cs, SCon{c, t}, fits))
