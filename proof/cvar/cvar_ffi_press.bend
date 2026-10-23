# eukhe: the proof of LAW cvar_ffi_press

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_cvar.bend as FCv
import ../../LAWS.bend as Laws
import ../base.bend as L

def Laws.cvar_ffi_press(bs, as, k, h):
  Equal.cong(Wr.Dec<Nat>, FCv.St & String, d => FCv.step.key(bs, as, d), Wr.get_nat(Wr.put_nat(k, "")), Wr.Got{k, ""}, Laws.wire_nat_round_trip(k, "", h))
