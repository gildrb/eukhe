# eukhe: the proof of LAW repeat_bounded

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

# PROOF of LAW repeat_bounded: the walk goes on, or stops with its count, which the spec clips to 1 to 2^32 - 1 (rp.bnd).

def Repeat.repeat_bounded(w, e):
  match w:
    case Rp.Walk{+want, +k, +first, +pend}:
      match e:
        case Rp.System{}:
          {==}
        case Rp.User{}:
          LARepeat.rp.bnd(k)
        case Rp.Result{r}:
          {==}
        case Rp.Called{+s}:
          LARepeat.rp.bnd_pick(Rp.repeats(want, first, s, pend), want, k, first, s, pend)
        case Rp.Said{}:
          LARepeat.rp.bnd(k)
        case Rp.End{}:
          LARepeat.rp.bnd(k)
