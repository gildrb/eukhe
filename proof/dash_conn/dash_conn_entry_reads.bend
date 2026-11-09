# eukhe: the proof of LAW dash_conn_entry_reads
#
# PROOF: each field reads back by the wire's round trips (LA.dcn.rt).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA

def DashConn.dash_conn_entry_reads(e, rest, h):
  LA.dcn.rt(e, rest, h)
