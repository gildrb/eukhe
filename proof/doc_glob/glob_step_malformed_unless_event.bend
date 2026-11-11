# eukhe: the proof of LAW glob_step_malformed_unless_event
#
# PROOF: stage by stage over the event's decoder (gsm.ev): each Nat or
# string it reads is the spelling of that value, then the rest, and fits
# (LAWS wire_nat_exact, wire_nat_decoded_fits, wire_str_exact,
# wire_str_decoded_fits); an event read whole, nothing after it, is the
# spelling of a path's time, a path whole or the page. A text it reads as
# no event answers the malformed-event error the premise excludes
# (gsm.main).

import Base
import ../../bend/doc_glob.bend as Gb
import ../../bend/ffi_doc_glob.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/doc_glob.bend as DocGlob
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../wire/base/spell.bend as LAWireSpell

def gsm.G(x: String) -> Type:
  &e: DocGlob.glob.Ev -> {x == DocGlob.glob.spell_ev(e) : String} & {DocGlob.glob.EvsFit([e]) == True{} : Bool}

# what the decoder read, when it read an event
def gsm.Ok(x: String, m: Maybe<&2, FGb.Ev>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      gsm.G(x)

# the page: the tag 2, nothing after
def gsm.show(+x: String, r: String, ex: {x == Wr.put_nat(2n, r) : String}) -> gsm.Ok(x, FGb.ev.end(Wr.end(r), FGb.Show{})):
  match r:
    case SNil{}:
      (DocGlob.glob.EShow{}, (ex, {==}))
    case SCon{h, t}:
      Unit{}

# a path's time: the tag 0, the time, nothing after
def gsm.met_end(+x: String, +r: String, ex: {x == Wr.put_nat(0n, r) : String}, +m: Nat, r2: String, e2: {r == Wr.put_nat(m, r2) : String}, fm: {LawsBase.wire_fits(m) == True{} : Bool}) -> gsm.Ok(x, FGb.ev.end(Wr.end(r2), FGb.Met{m})):
  match r2:
    case SNil{}:
      +eq = Equal.trans(String, x, Wr.put_nat(0n, r), Wr.put_nat(0n, Wr.put_nat(m, "")), ex, Equal.cong(String, String, z => Wr.put_nat(0n, z), r, Wr.put_nat(m, ""), e2))
      +fit = LAWireSpell.ws_and_tt(Bool.and(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(0n)), True{}), True{}, LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(0n)), True{}, LAWireSpell.ws_and_tt(LawsBase.wire_fits(m), LawsBase.wire_fits(0n), fm, {==}), {==}), {==})
      (DocGlob.glob.EMet{DocGlob.glob.Hit{m, ""}}, (eq, fit))
    case SCon{h, t}:
      Unit{}

def gsm.met(+x: String, +r: String, ex: {x == Wr.put_nat(0n, r) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> gsm.Ok(x, FGb.ev.met(d)):
  match d:
    case Wr.Got{+m, +r2}:
      +ee = ed
      gsm.met_end(x, r, ex, m, r2, Wire.wire_nat_exact(r, m, r2, ee), Wire.wire_nat_decoded_fits(r, m, r2, ee))
    case Wr.Bad{}:
      Unit{}

# a path whole: the tag 1, the time, the path, nothing after
def gsm.add_end(+x: String, +r: String, ex: {x == Wr.put_nat(1n, r) : String}, +m: Nat, +r2: String, e2: {r == Wr.put_nat(m, r2) : String}, fm: {LawsBase.wire_fits(m) == True{} : Bool}, +p: String, r3: String, e3: {r2 == Wr.put_str(p, r3) : String}, fp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}) -> gsm.Ok(x, FGb.ev.end(Wr.end(r3), FGb.Add{m, p})):
  match r3:
    case SNil{}:
      +e4 = Equal.trans(String, r, Wr.put_nat(m, r2), Wr.put_nat(m, Wr.put_str(p, "")), e2, Equal.cong(String, String, z => Wr.put_nat(m, z), r2, Wr.put_str(p, ""), e3))
      +eq = Equal.trans(String, x, Wr.put_nat(1n, r), Wr.put_nat(1n, Wr.put_nat(m, Wr.put_str(p, ""))), ex, Equal.cong(String, String, z => Wr.put_nat(1n, z), r, Wr.put_nat(m, Wr.put_str(p, "")), e4))
      +fit = LAWireSpell.ws_and_tt(Bool.and(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), True{}), True{}, LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), True{}, LAWireSpell.ws_and_tt(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p)), fm, fp), {==}), {==})
      (DocGlob.glob.EAdd{DocGlob.glob.Hit{m, p}}, (eq, fit))
    case SCon{h, t}:
      Unit{}

def gsm.path(+x: String, +r: String, ex: {x == Wr.put_nat(1n, r) : String}, +m: Nat, +r2: String, e2: {r == Wr.put_nat(m, r2) : String}, fm: {LawsBase.wire_fits(m) == True{} : Bool}, d: Wr.Dec<String>, ed: {Wr.get_str(r2) == d : Wr.Dec<String>}) -> gsm.Ok(x, FGb.ev.path(m, d)):
  match d:
    case Wr.Got{+p, +r3}:
      +ee = ed
      gsm.add_end(x, r, ex, m, r2, e2, fm, p, r3, Wire.wire_str_exact(r2, p, r3, ee), Wire.wire_str_decoded_fits(r2, p, r3, ee))
    case Wr.Bad{}:
      Unit{}

def gsm.add(+x: String, +r: String, ex: {x == Wr.put_nat(1n, r) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> gsm.Ok(x, FGb.ev.add(d)):
  match d:
    case Wr.Got{+m, +r2}:
      +ee = ed
      gsm.path(x, r, ex, m, r2, Wire.wire_nat_exact(r, m, r2, ee), Wire.wire_nat_decoded_fits(r, m, r2, ee), Wr.get_str(r2), {==})
    case Wr.Bad{}:
      Unit{}

# whatever the decoder reads as an event is its spelling and fits
def gsm.ev(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}) -> gsm.Ok(x, FGb.ev(d)):
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          gsm.met(x, r, Wire.wire_nat_exact(x, 0n, r, ed), Wr.get_nat(r), {==})
        case 1n:
          gsm.add(x, r, Wire.wire_nat_exact(x, 1n, r, ed), Wr.get_nat(r), {==})
        case 2n:
          gsm.show(x, r, Wire.wire_nat_exact(x, 2n, r, ed))
        case 3n+y:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# no event answers the malformed-event error
def gsm.main(+s: Nat, +k: Nat, +c: Nat, +len: Nat, +low: Nat, +xs: List<&2, Gb.It>, +x: String, m: Maybe<&2, FGb.Ev>, ok: gsm.Ok(x, m), other: {String.eq(DocGlob.glob.Snd(FGb.step.ev(FGb.Gl{s, k, c, len, low, xs}, m)), Wr.err("doc_glob: malformed event")) == False{} : Bool}) -> gsm.G(x):
  match m:
    case None{}:
      LAWireSpell.ws_absurd(gsm.G(x), other)
    case Some{v}:
      ok

def DocGlob.glob_step_malformed_unless_event(s, k, c, len, low, xs, x, other):
  gsm.main(s, k, c, len, low, xs, x, FGb.ev(Wr.get_nat(x)), gsm.ev(x, Wr.get_nat(x), {==}), other)
