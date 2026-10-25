# eukhe: the proof of LAW dash_conn_entry_reads
#
# PROOF: each field reads back by the wire's round trips (LA.dcn.rt).

import Base
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA

def DashConn.dash_conn_entry_reads(e, rest, h):
  LA.dcn.rt(e, rest, h)
