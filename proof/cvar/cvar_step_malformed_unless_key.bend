# eukhe: the proof of LAW cvar_step_malformed_unless_key
#
# PROOF: a key read is spelled and fits (wire_nat_exact,
# wire_nat_decoded_fits); when none is read the press answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/base/spell.bend as LAWireSpell

def csmu.G(+s: String) -> Type:
  &k: Nat -> &rest: String -> {(s, LawsBase.wire_fits(k)) == (Wr.put_nat(k, rest), True{}) : String & Bool}

def csmu.eq(+s: String, +k: Nat, +rest: String, e1: {s == Wr.put_nat(k, rest) : String}, e2: {LawsBase.wire_fits(k) == True{} : Bool}) -> {(s, LawsBase.wire_fits(k)) == (Wr.put_nat(k, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Wr.put_nat(k, rest), e1) : {(_, LawsBase.wire_fits(k)) == (Wr.put_nat(k, rest), True{}) : String & Bool}
  %Equal.sym(Bool, LawsBase.wire_fits(k), True{}, e2) : {(Wr.put_nat(k, rest), _) == (Wr.put_nat(k, rest), True{}) : String & Bool}
  {==}

def csmu.main(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, +s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, other: {String.eq(CvarEntry.cvar_reply_of(FCv.step.key(bs, as, d)), Wr.err("cvar: malformed key")) == False{} : Bool}) -> csmu.G(s):
  match d:
    case Wr.Got{+k, +rest}:
      +e = ed
      (k, (rest, csmu.eq(s, k, rest, Wire.wire_nat_exact(s, k, rest, e), Wire.wire_nat_decoded_fits(s, k, rest, e))))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(csmu.G(s), other)

def CvarEntry.cvar_step_malformed_unless_key(bs, as, s, other):
  csmu.main(bs, as, s, Wr.get_nat(s), {==}, other)
