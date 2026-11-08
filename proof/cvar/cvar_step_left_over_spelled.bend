# eukhe: the proof of LAW cvar_step_left_over_spelled
#
# PROOF: the key reads back with the rest untouched (wire_nat_round_trip);
# the rest is not empty, so the press answers the left-over error.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ../../laws/wire.bend as Wire

def CvarEntry.cvar_step_left_over_spelled(bs, as, k, fits, c, t):
  Equal.cong(Wr.Dec<Nat>, FCv.St & String, d => FCv.step.key(bs, as, d), Wr.get_nat(Wr.put_nat(k, SCon{c, t})), Wr.Got{k, SCon{c, t}}, Wire.wire_nat_round_trip(k, SCon{c, t}, fits))
