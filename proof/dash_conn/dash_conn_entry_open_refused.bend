# eukhe: the proof of LAW dash_conn_entry_open_refused
#
# PROOF: by cases on the input: it is not empty, so the open is refused
# (computes); the empty input contradicts the premise.

import Base
import ../../bend/ffi_dash.bend as FDa
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA

def dcor.go(s: String, h: {String.is_empty(s) == False{} : Bool}) -> {FDa.open(s) == (FDa.Refused{}, SCon{'E', SCon{' ', "dash: the open takes no input"}}) : FDa.St & String}:
  match s:
    case SNil{}:
      LA.dcn.absurdT({FDa.open(SNil{}) == (FDa.Refused{}, SCon{'E', SCon{' ', "dash: the open takes no input"}}) : FDa.St & String}, h)
    case SCon{c, t}:
      {==}

def DashConn.dash_conn_entry_open_refused(s, h):
  dcor.go(s, h)
