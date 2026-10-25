# eukhe: the proof of LAW dash_conn_entry_answers
#
# PROOF: the step is the spec's on every input (dash_conn_entry_exact),
# and the spec reads the spelled event back whole with nothing left
# (dash_conn_entry_reads).

import Base
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../bend/dash.bend as Da
import ../../laws/dash_conn.bend as DashConn
import ./dash_conn_entry_exact.bend as PDashConnEntryExact
import ./dash_conn_entry_reads.bend as PDashConnEntryReads

def DashConn.dash_conn_entry_answers(c, e, h):
  %Equal.sym(FDa.St & String, FDa.step(FDa.Live{c}, DashConn.sp_w_ev(e, "")), DashConn.cspec(c, DashConn.sp_w_ev(e, "")), DashConn.dash_conn_entry_exact(c, DashConn.sp_w_ev(e, ""))) : {_ == DashConn.cs_reply(DashConn.sp_cstep(c, e)) : FDa.St & String}
  %Equal.sym(Wr.Dec<Da.CEv>, DashConn.read_ev(DashConn.sp_w_ev(e, "")), Wr.Got{e, ""}, DashConn.dash_conn_entry_reads(e, "", h)) : {DashConn.cs.run(c, _) == DashConn.cs_reply(DashConn.sp_cstep(c, e)) : FDa.St & String}
  {==}
