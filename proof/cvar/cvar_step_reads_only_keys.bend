# eukhe: the proof of LAW cvar_step_reads_only_keys
#
# PROOF: a key read is spelled and fits (wire_nat_exact,
# wire_nat_decoded_fits); a reply that is no error comes from a key read
# whole, nothing left, and is put_exp of the press, the spelled expansion
# (cvs.exp).

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
import ./base/spell.bend as LS

def csro.G(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, s: String, a: String) -> Type:
  &k: Nat -> {(s, (LawsBase.wire_fits(k), a)) == (Wr.put_nat(k, ""), (True{}, CvarEntry.cvar_spell_exp(Cv.press(bs, k, as), ""))) : String & (Bool & String)}

def csro.eq(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, +s: String, +k: Nat, +a: String, e: {s == Wr.put_nat(k, "") : String}, f: {LawsBase.wire_fits(k) == True{} : Bool}, ea: {a == CvarEntry.cvar_spell_exp(Cv.press(bs, k, as), "") : String}) -> {(s, (LawsBase.wire_fits(k), a)) == (Wr.put_nat(k, ""), (True{}, CvarEntry.cvar_spell_exp(Cv.press(bs, k, as), ""))) : String & (Bool & String)}:
  %Equal.sym(String, s, Wr.put_nat(k, ""), e) : {(_, (LawsBase.wire_fits(k), a)) == (Wr.put_nat(k, ""), (True{}, CvarEntry.cvar_spell_exp(Cv.press(bs, k, as), ""))) : String & (Bool & String)}
  %Equal.sym(Bool, LawsBase.wire_fits(k), True{}, f) : {(Wr.put_nat(k, ""), (_, a)) == (Wr.put_nat(k, ""), (True{}, CvarEntry.cvar_spell_exp(Cv.press(bs, k, as), ""))) : String & (Bool & String)}
  %Equal.sym(String, a, CvarEntry.cvar_spell_exp(Cv.press(bs, k, as), ""), ea) : {(Wr.put_nat(k, ""), (True{}, _)) == (Wr.put_nat(k, ""), (True{}, CvarEntry.cvar_spell_exp(Cv.press(bs, k, as), ""))) : String & (Bool & String)}
  {==}

def csro.fin(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, +s: String, +k: Nat, r: String, pre: {s == Wr.put_nat(k, r) : String}, f: {LawsBase.wire_fits(k) == True{} : Bool}, ok: {LawsBase.wire_opens_err(CvarEntry.cvar_reply_of(FCv.step.key(bs, as, Wr.Got{k, r}))) == False{} : Bool}) -> csro.G(bs, as, s, CvarEntry.cvar_reply_of(FCv.step.key(bs, as, Wr.Got{k, r}))):
  match r:
    case SNil{}:
      (k, csro.eq(bs, as, s, k, FCv.put_exp(Cv.press(bs, k, as), ""), pre, f, LS.cvs.exp(Cv.press(bs, k, as), "")))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(csro.G(bs, as, s, Wr.err("cvar: input left over")), ok)

def csro.main(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, +s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(CvarEntry.cvar_reply_of(FCv.step.key(bs, as, d))) == False{} : Bool}) -> csro.G(bs, as, s, CvarEntry.cvar_reply_of(FCv.step.key(bs, as, d))):
  match d:
    case Wr.Got{+k, +r}:
      +e = ed
      csro.fin(bs, as, s, k, r, Wire.wire_nat_exact(s, k, r, e), Wire.wire_nat_decoded_fits(s, k, r, e), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(csro.G(bs, as, s, Wr.err("cvar: malformed key")), ok)

def CvarEntry.cvar_step_reads_only_keys(bs, as, s, ok):
  csro.main(bs, as, s, Wr.get_nat(s), {==}, ok)
