# eukhe: the proof of LAW repeat_steps

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

# PROOF of LAW repeat_steps: the walk from any state answers 1, its rounds and the rounds of the spec's pieces that repeat (rp.walk); a fresh walk has none.

def Repeat.repeat_steps(want, es):
  LARepeat.rp.walk(es, want, 0n, None{}, Nil{})
