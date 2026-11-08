# eukhe: the proof of LAW cvar_step_answers_spelled
#
# PROOF: the key reads back (wire_nat_round_trip); the reply put_exp is the
# spelled expansion (cvs.exp).

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ../../laws/wire.bend as Wire
import ./base/spell.bend as LS

def CvarEntry.cvar_step_answers_spelled(bs, as, k, fits):
  %LS.cvs.exp(Cv.press(bs, k, as), "") : {FCv.step(FCv.Table{bs, as}, Wr.put_nat(k, "")) == (FCv.Table{bs, as}, _) : FCv.St & String}
  Equal.cong(Wr.Dec<Nat>, FCv.St & String, d => FCv.step.key(bs, as, d), Wr.get_nat(Wr.put_nat(k, "")), Wr.Got{k, ""}, Wire.wire_nat_round_trip(k, "", fits))
