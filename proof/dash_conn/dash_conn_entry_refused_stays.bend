# eukhe: the proof of LAW dash_conn_entry_refused_stays
#
# PROOF: an open with input is refused (its input is not empty); a refused
# socket answers each step the refused error and stays refused (ers.go, by
# induction on the inputs).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA

def ers.go(ins: List<&2, String>, +out: String) -> {DashConn.cs_raw(ins, (FDa.Refused{}, out)) == out <> DashConn.sp_shut(ins) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case i <> t:
      Equal.cong(List<&2, String>, List<&2, String>, z => out <> z, DashConn.cs_raw(t, (FDa.Refused{}, SCon{'E', SCon{' ', "dash: the open was refused"}})), SCon{'E', SCon{' ', "dash: the open was refused"}} <> DashConn.sp_shut(t), ers.go(t, SCon{'E', SCon{' ', "dash: the open was refused"}}))

def DashConn.dash_conn_entry_refused_stays(s, ins, h):
  %Equal.sym(Bool, String.is_empty(s), False{}, h) : {DashConn.cs_raw(ins, FDa.open.end(_)) == DashConn.sp_open_refused() <> DashConn.sp_shut(ins) : List<&2, String>}
  ers.go(ins, DashConn.sp_open_refused())
