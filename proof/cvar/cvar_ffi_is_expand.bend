# eukhe: the proof of LAW cvar_ffi_is_expand

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_cvar.bend as FCv
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.cvar_ffi_is_expand(as, cs, h):
  Equal.cong(Wr.Dec<FCv.Xreq>, String, d => FCv.ffi.go(d), FCv.get_xreq(FCv.put_xreq(FCv.Xreq{as, cs}, "")), Wr.Got{FCv.Xreq{as, cs}, ""}, LA.pvf.xreq_rt(as, cs, "", h))
