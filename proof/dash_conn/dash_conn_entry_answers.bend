# eukhe: the proof of LAW dash_conn_entry_answers
#
# PROOF: the shipped decoder reads the spelled event back whole with
# nothing left (dash_conn_entry_reads), so the step answers the model's
# step with its verdict spelled (LA.dcn.reply).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA
import ./dash_conn_entry_reads.bend as PDashConnEntryReads

def DashConn.dash_conn_entry_answers(c, e, h):
  %Equal.sym(Wr.Dec<Da.CEv>, FDa.get_ev(DashConn.sp_w_ev(e, "")), Wr.Got{e, ""}, DashConn.dash_conn_entry_reads(e, "", h)) : {FDa.step.ev(c, _) == DashConn.cs_reply(Da.cstep(c, e)) : FDa.St & String}
  LA.dcn.reply(Da.cstep(c, e))
