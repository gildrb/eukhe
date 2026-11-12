# eukhe: the proof of LAW dash_conn_first_refused
#
# PROOF: a waiting socket's first frame takes the gate's pass; a refusal
# closes with its text (computes).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA

def DashConn.dash_conn_first_refused(x, f, m, t, refused):
  %Equal.sym(Da.Pass, Da.gate(x, f, m), Da.Refuse{t}, refused) : {Da.first.pass(_) == (Da.Closed{}, Da.VRefuse{t}) : Da.Conn & Da.Verdict}
  {==}
