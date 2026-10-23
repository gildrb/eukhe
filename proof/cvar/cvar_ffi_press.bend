# eukhe: the proof of LAW cvar_ffi_press

import Base
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar.bend as Cvar
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

def Cvar.cvar_ffi_press(bs, as, k, h):
  Equal.cong(Wr.Dec<Nat>, FCv.St & String, d => FCv.step.key(bs, as, d), Wr.get_nat(Wr.put_nat(k, "")), Wr.Got{k, ""}, Wire.wire_nat_round_trip(k, "", h))
