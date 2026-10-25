# eukhe: the proof of LAW dash_conn_refusal_closes
#
# PROOF: by cases on the socket and the event: a pass that refuses closes
# (dcr.first_closes, dcr.later_closes); every other refusal closes by
# computation; a closed socket answers `closed`, no refusal.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA

def drc.go(c: Da.Conn, e: Da.CEv, refused: {DashConn.cv_is_refuse(DashConn.cv_verdict(Da.cstep(c, e))) == True{} : Bool}) -> {DashConn.cv_is_closed(DashConn.cv_conn(Da.cstep(c, e))) == True{} : Bool}:
  match c:
    case Da.Waiting{}:
      match e:
        case Da.CFirst{x, f, m}:
          LA.dcr.first_closes(Da.gate(x, f, m), refused)
        case Da.CFrame{f, m}:
          {==}
    case Da.Paired{}:
      match e:
        case Da.CFirst{x, f, m}:
          {==}
        case Da.CFrame{f, m}:
          LA.dcr.later_closes(Da.frame(f, m), refused)
    case Da.Closed{}:
      {==}

def DashConn.dash_conn_refusal_closes(c, e, refused):
  drc.go(c, e, refused)
