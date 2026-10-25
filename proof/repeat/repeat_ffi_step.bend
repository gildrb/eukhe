# eukhe: the proof of LAW repeat_ffi_step

import Base
import ../../bend/repeat.bend as Rp
import ../../bend/ffi_repeat.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../../laws/repeat.bend as Repeat
import ./base.bend as LARepeat

# PROOF of LAW repeat_ffi_step: the message reads back with nothing left (rp.ev_rt) and the stepper's reply writer is the spec's speller (rp.of).

def Repeat.repeat_ffi_step(w, e, fits):
  %LARepeat.rp.ev_rt(e, "", fits) : {FRp.step.ev(w, _) == Repeat.spell_next(Rp.step(w, e)) : FRp.St & String}
  LARepeat.rp.of(Rp.step(w, e))
