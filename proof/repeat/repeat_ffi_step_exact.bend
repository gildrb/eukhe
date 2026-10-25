# eukhe: the proof of LAW repeat_ffi_step_exact

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

# PROOF of LAW repeat_ffi_step_exact: what the decoder reads is spelled and its id fits (rp.pe); a message with input left over or a malformed one answers the error form.

def rp.sex_end(-s: String, r: String, +w: Rp.Walk, +e: Rp.Ev, p: {s == Repeat.spell_ev(e, r) : String} & {Repeat.ev_fits(e) == True{} : Bool}, ok: {LawsBase.wire_opens_err(Repeat.reply(FRp.step.end(Wr.end(r), w, e))) == False{} : Bool}) -> Sigma<&1, &1, Rp.Ev, x => {s == Repeat.spell_ev(x, "") : String} & {Repeat.ev_fits(x) == True{} : Bool}>:
  match r:
    case SNil{}:
      (e, p)
    case SCon{h, t}:
      LARepeat.rp.absurd_t(Sigma<&1, &1, Rp.Ev, x => {s == Repeat.spell_ev(x, "") : String} & {Repeat.ev_fits(x) == True{} : Bool}>, ok)

def rp.sex(-s: String, +w: Rp.Walk, d: Wr.Dec<Rp.Ev>, p: LARepeat.rp.PE(s, d), ok: {LawsBase.wire_opens_err(Repeat.reply(FRp.step.ev(w, d))) == False{} : Bool}) -> Sigma<&1, &1, Rp.Ev, x => {s == Repeat.spell_ev(x, "") : String} & {Repeat.ev_fits(x) == True{} : Bool}>:
  match d:
    case Wr.Got{+e, +r}:
      rp.sex_end(s, r, w, e, p, ok)
    case Wr.Bad{}:
      LARepeat.rp.absurd_t(Sigma<&1, &1, Rp.Ev, x => {s == Repeat.spell_ev(x, "") : String} & {Repeat.ev_fits(x) == True{} : Bool}>, ok)

def Repeat.repeat_ffi_step_exact(w, s, ok):
  rp.sex(s, w, FRp.get_ev(Wr.get_nat(s)), LARepeat.rp.pe(s), ok)
