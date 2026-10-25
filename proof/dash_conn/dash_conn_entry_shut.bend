# eukhe: the proof of LAW dash_conn_entry_shut
#
# PROOF: a refused open's step does not look at the input: it computes.

import Base
import ../../bend/ffi_dash.bend as FDa
import ../../laws/dash_conn.bend as DashConn

def DashConn.dash_conn_entry_shut(s):
  {==}
