# eukhe: the proof of LAW repeat_ffi_step_errors

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

# PROOF of LAW repeat_ffi_step_errors: a message the decoder reads whole answers the model's step, never the error form (rp.of_not_err); every other step keeps the walk and answers the malformed error form.

def rp.ser_end(r: String, +w: Rp.Walk, +e: Rp.Ev, er: {LawsBase.wire_opens_err(Repeat.reply(FRp.step.end(Wr.end(r), w, e))) == True{} : Bool}) -> {FRp.step.end(Wr.end(r), w, e) == (FRp.Live{w}, Wr.err("repeat: malformed message")) : FRp.St & String}:
  match r:
    case SNil{}:
      LARepeat.rp.absurd({FRp.step.of(Rp.step(w, e)) == (FRp.Live{w}, Wr.err("repeat: malformed message")) : FRp.St & String}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(Repeat.reply(FRp.step.of(Rp.step(w, e)))), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(Repeat.reply(FRp.step.of(Rp.step(w, e)))), False{}, LARepeat.rp.of_not_err(Rp.step(w, e))), er))
    case SCon{h, t}:
      {==}

def rp.ser(+w: Rp.Walk, d: Wr.Dec<Rp.Ev>, er: {LawsBase.wire_opens_err(Repeat.reply(FRp.step.ev(w, d))) == True{} : Bool}) -> {FRp.step.ev(w, d) == (FRp.Live{w}, Wr.err("repeat: malformed message")) : FRp.St & String}:
  match d:
    case Wr.Got{+e, +r}:
      rp.ser_end(r, w, e, er)
    case Wr.Bad{}:
      {==}

def Repeat.repeat_ffi_step_errors(w, s, e):
  rp.ser(w, FRp.get_ev(Wr.get_nat(s)), e)
