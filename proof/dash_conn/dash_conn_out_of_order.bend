# eukhe: the proof of LAW dash_conn_out_of_order
#
# PROOF: both cases compute.

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA

def DashConn.dash_conn_out_of_order(x, f, m):
  ({==}, {==})
