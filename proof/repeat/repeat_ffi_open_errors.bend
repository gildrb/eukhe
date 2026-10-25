# eukhe: the proof of LAW repeat_ffi_open_errors

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

# PROOF of LAW repeat_ffi_open_errors: an open the decoder reads whole answers an empty reply, never the error form; every other open is refused.

def rp.oer_end(r: String, +want: Nat, e: {LawsBase.wire_opens_err(Repeat.reply(FRp.open.end(Wr.end(r), want))) == True{} : Bool}) -> {FRp.open.end(Wr.end(r), want) == (FRp.Shut{}, Wr.err("repeat: malformed open")) : FRp.St & String}:
  match r:
    case SNil{}:
      LARepeat.rp.absurd({(FRp.Live{Rp.start(want)}, "") == (FRp.Shut{}, Wr.err("repeat: malformed open")) : FRp.St & String}, e)
    case SCon{h, t}:
      {==}

def rp.oer(d: Wr.Dec<Nat>, e: {LawsBase.wire_opens_err(Repeat.reply(FRp.open.go(d))) == True{} : Bool}) -> {FRp.open.go(d) == (FRp.Shut{}, Wr.err("repeat: malformed open")) : FRp.St & String}:
  match d:
    case Wr.Got{+want, +r}:
      rp.oer_end(r, want, e)
    case Wr.Bad{}:
      {==}

def Repeat.repeat_ffi_open_errors(s, e):
  rp.oer(Wr.get_nat(s), e)
