# eukhe: the proof of LAW repeat_step_exact

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

# PROOF of LAW repeat_step_exact: per message both sides compute; a reply with calls goes on exactly when the code's and the spec's tests agree (rp.sx_called), and every stop counts as the spec clips (rp.count).

def Repeat.repeat_step_exact(w, e):
  match w:
    case Rp.Walk{+want, +k, +first, +pend}:
      match e:
        case Rp.System{}:
          {==}
        case Rp.User{}:
          LARepeat.rp.stop_eq(k)
        case Rp.Result{r}:
          {==}
        case Rp.Called{+s}:
          LARepeat.rp.sx_called(first, want, k, s, pend)
        case Rp.Said{}:
          LARepeat.rp.stop_eq(k)
        case Rp.End{}:
          LARepeat.rp.stop_eq(k)
