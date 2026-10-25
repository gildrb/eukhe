# eukhe: the proof of LAW dash_conn_closed_stays
#
# PROOF: a closed socket's step does not look at the event: it computes.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash_conn.bend as DashConn

def DashConn.dash_conn_closed_stays(e):
  {==}
