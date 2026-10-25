# eukhe: the proof of LAW repeat_ffi_open

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

# PROOF of LAW repeat_ffi_open: the id reads back (wire_nat_round_trip) with nothing left.

def Repeat.repeat_ffi_open(want, fits):
  %LARepeat.rp.nat(want, "", fits) : {FRp.open.go(_) == (FRp.Live{Rp.start(want)}, "") : FRp.St & String}
  {==}
