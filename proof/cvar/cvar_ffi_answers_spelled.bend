# eukhe: the proof of LAW cvar_ffi_answers_spelled
#
# PROOF: the spelled request is the entry's own encoding (cvs.xreq), which
# reads back whole (LA.pvf.xreq_rt); the reply put_exp is the spelled
# expansion (cvs.exp).

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ./base.bend as LA
import ./base/spell.bend as LS

def CvarEntry.cvar_ffi_answers_spelled(as, cs, fits):
  %LS.cvs.xreq(as, cs, "") : {FCv.ffi(_) == CvarEntry.cvar_spell_exp(Cv.expand(cs, as), "") : String}
  %LS.cvs.exp(Cv.expand(cs, as), "") : {FCv.ffi(FCv.put_xreq(FCv.Xreq{as, cs}, "")) == _ : String}
  Equal.cong(Wr.Dec<FCv.Xreq>, String, d => FCv.ffi.go(d), FCv.get_xreq(FCv.put_xreq(FCv.Xreq{as, cs}, "")), Wr.Got{FCv.Xreq{as, cs}, ""}, LA.pvf.xreq_rt(as, cs, "", fits))
