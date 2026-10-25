# eukhe: the proof of LAW dash_conn_entry_exact
#
# PROOF: the stepper's decoder is the laws' reader (LA.dcn.read); on an
# event read whole its step is the spec's (dash_conn_step_spec) and its
# verdict encoder the spec's speller (LA.dcn.reply); a malformed event or
# input left over answers the same error form on both sides.

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/dash_conn.bend as DashConn
import ./dash_conn_step_spec.bend as PDashConnStepSpec
import ./base.bend as LA

def dce.end(b: Bool, +c: Da.Conn, +e: Da.CEv) -> {FDa.step.end(b, c, e) == DashConn.cs.end(b, c, e) : FDa.St & String}:
  match b:
    case True{}:
      %DashConn.dash_conn_step_spec(c, e) : {FDa.step.reply(Da.cstep(c, e)) == DashConn.cs_reply(_) : FDa.St & String}
      LA.dcn.reply(Da.cstep(c, e))
    case False{}:
      {==}

def dce.run(+c: Da.Conn, r: Wr.Dec<Da.CEv>) -> {FDa.step.ev(c, r) == DashConn.cs.run(c, r) : FDa.St & String}:
  match r:
    case Wr.Got{e, s}:
      dce.end(Wr.end(s), c, e)
    case Wr.Bad{}:
      {==}

def DashConn.dash_conn_entry_exact(c, s):
  %LA.dcn.read(s) : {FDa.step.ev(c, FDa.get_ev(s)) == DashConn.cs.run(c, _) : FDa.St & String}
  dce.run(c, FDa.get_ev(s))
