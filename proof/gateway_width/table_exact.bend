# eukhe: the proof of LAW table_exact

import Base
import ../../bend/gateway_width.bend as Gw
import ../../laws/gateway_width.bend as GatewayWidth
import ./base.bend as LA

def GatewayWidth.table_exact(rows):
  LA.gw.sp_table(Gw.Display{}, rows)
