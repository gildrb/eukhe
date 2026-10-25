# eukhe: the proof of LAW dash_conn_nothing_before_pairing
#
# PROOF: a waiting socket's first frame pairs or refuses
# (dcr.first_not_run); a frame before it is refused (computes).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA

def dnb.go(e: Da.CEv) -> {DashConn.cv_is_run(DashConn.cv_verdict(Da.cstep(Da.Waiting{}, e))) == False{} : Bool}:
  match e:
    case Da.CFirst{x, f, m}:
      LA.dcr.first_not_run(Da.gate(x, f, m))
    case Da.CFrame{f, m}:
      {==}

def DashConn.dash_conn_nothing_before_pairing(e):
  dnb.go(e)
