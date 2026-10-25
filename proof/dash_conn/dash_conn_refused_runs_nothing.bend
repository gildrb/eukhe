# eukhe: the proof of LAW dash_conn_refused_runs_nothing
#
# PROOF: a refusal closes the socket (dash_conn_refusal_closes), and a
# closed socket runs and opens nothing, whatever comes (dcr.closed_quiet:
# by induction on the events).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash_conn.bend as DashConn
import ./dash_conn_refusal_closes.bend as PDashConnRefusalCloses
import ./base.bend as LA

def DashConn.dash_conn_refused_runs_nothing(c, e, es, refused):
  LA.dcr.closed_quiet(DashConn.cv_conn(Da.cstep(c, e)), es, DashConn.dash_conn_refusal_closes(c, e, refused))
