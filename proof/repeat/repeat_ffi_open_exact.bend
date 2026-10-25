# eukhe: the proof of LAW repeat_ffi_open_exact

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

# PROOF of LAW repeat_ffi_open_exact: what the decoder reads is spelled and fits (rp.pnf); an open with input left over or a malformed id answers the error form.

def rp.oex_end(-s: String, r: String, +want: Nat, p: {s == Wr.put_nat(want, r) : String} & {LawsBase.wire_fits(want) == True{} : Bool}, ok: {LawsBase.wire_opens_err(Repeat.reply(FRp.open.end(Wr.end(r), want))) == False{} : Bool}) -> Sigma<&1, &1, Nat, x => {s == Repeat.spell_open(x) : String} & {LawsBase.wire_fits(x) == True{} : Bool}>:
  match r:
    case SNil{}:
      (want, p)
    case SCon{h, t}:
      LARepeat.rp.absurd_t(Sigma<&1, &1, Nat, x => {s == Repeat.spell_open(x) : String} & {LawsBase.wire_fits(x) == True{} : Bool}>, ok)

def rp.oex(-s: String, d: Wr.Dec<Nat>, p: LARepeat.rp.PNF(s, d), ok: {LawsBase.wire_opens_err(Repeat.reply(FRp.open.go(d))) == False{} : Bool}) -> Sigma<&1, &1, Nat, x => {s == Repeat.spell_open(x) : String} & {LawsBase.wire_fits(x) == True{} : Bool}>:
  match d:
    case Wr.Got{+want, +r}:
      rp.oex_end(s, r, want, p, ok)
    case Wr.Bad{}:
      LARepeat.rp.absurd_t(Sigma<&1, &1, Nat, x => {s == Repeat.spell_open(x) : String} & {LawsBase.wire_fits(x) == True{} : Bool}>, ok)

def Repeat.repeat_ffi_open_exact(s, ok):
  rp.oex(s, Wr.get_nat(s), LARepeat.rp.pnf(s), ok)
