# eukhe: the proof of LAW glob_open_malformed_unless_open
#
# PROOF: stage by stage over the open's decoder. Each Nat it reads is the
# spelling of that Nat, then the rest, and fits (LAWS wire_nat_exact,
# wire_nat_decoded_fits); a limit tag past 1, a Bad read or input left
# over refuses the open, whose reply is then the malformed-open error the
# premise excludes. So the open is the skip, then the limit tag 0, or 1
# and the limit, then nothing: the spelling of glob.spell_open.

import Base
import ../../bend/ffi_doc_glob.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/doc_glob.bend as DocGlob
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/base/spell.bend as LAWireSpell

def gom.G(x: String) -> Type:
  &s: Nat -> &lim: Maybe<&2, Nat> -> {x == DocGlob.glob.spell_open(s, lim) : String} & {Bool.and(LawsBase.wire_fits(s), LawsBase.core_mfits(lim)) == True{} : Bool}

# the limit 1 then l, nothing after
def gom.lim(+x: String, +s: Nat, +r: String, ex: {x == Wr.put_nat(s, r) : String}, fs: {LawsBase.wire_fits(s) == True{} : Bool}, +r2: String, er: {r == Wr.put_nat(1n, r2) : String}, +l: Nat, r3: String, e3: {r2 == Wr.put_nat(l, r3) : String}, fl: {LawsBase.wire_fits(l) == True{} : Bool}, other: {String.eq(DocGlob.glob.Snd(FGb.open.lim(s, FGb.lim.end(Wr.end(r3), Some{l}))), Wr.err("doc_glob: malformed open")) == False{} : Bool}) -> gom.G(x):
  match r3:
    case SNil{}:
      +e2 = Equal.trans(String, r, Wr.put_nat(1n, r2), Wr.put_nat(1n, Wr.put_nat(l, "")), er, Equal.cong(String, String, z => Wr.put_nat(1n, z), r2, Wr.put_nat(l, ""), e3))
      (s, (Some{l}, (Equal.trans(String, x, Wr.put_nat(s, r), Wr.put_nat(s, Wr.put_nat(1n, Wr.put_nat(l, ""))), ex, Equal.cong(String, String, z => Wr.put_nat(s, z), r, Wr.put_nat(1n, Wr.put_nat(l, "")), e2)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(s), LawsBase.wire_fits(l), fs, fl))))
    case SCon{c, t}:
      LAWireSpell.ws_absurd(gom.G(x), other)

# the limit tag 1, then the limit
def gom.one(+x: String, +s: Nat, +r: String, ex: {x == Wr.put_nat(s, r) : String}, fs: {LawsBase.wire_fits(s) == True{} : Bool}, +r2: String, er: {r == Wr.put_nat(1n, r2) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(r2) == d : Wr.Dec<Nat>}, other: {String.eq(DocGlob.glob.Snd(FGb.open.lim(s, FGb.lim.one(d))), Wr.err("doc_glob: malformed open")) == False{} : Bool}) -> gom.G(x):
  match d:
    case Wr.Got{+l, +r3}:
      +ee = ed
      gom.lim(x, s, r, ex, fs, r2, er, l, r3, Wire.wire_nat_exact(r2, l, r3, ee), Wire.wire_nat_decoded_fits(r2, l, r3, ee), other)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(gom.G(x), other)

# the limit tag 0, nothing after
def gom.none(+x: String, +s: Nat, +r: String, ex: {x == Wr.put_nat(s, r) : String}, fs: {LawsBase.wire_fits(s) == True{} : Bool}, r2: String, er: {r == Wr.put_nat(0n, r2) : String}, other: {String.eq(DocGlob.glob.Snd(FGb.open.lim(s, FGb.lim.end(Wr.end(r2), None{}))), Wr.err("doc_glob: malformed open")) == False{} : Bool}) -> gom.G(x):
  match r2:
    case SNil{}:
      (s, (None{}, (Equal.trans(String, x, Wr.put_nat(s, r), Wr.put_nat(s, Wr.put_nat(0n, "")), ex, Equal.cong(String, String, z => Wr.put_nat(s, z), r, Wr.put_nat(0n, ""), er)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(s), True{}, fs, {==}))))
    case SCon{c, t}:
      LAWireSpell.ws_absurd(gom.G(x), other)

# the limit's tag
def gom.tag(+x: String, +s: Nat, +r: String, ex: {x == Wr.put_nat(s, r) : String}, fs: {LawsBase.wire_fits(s) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}, other: {String.eq(DocGlob.glob.Snd(FGb.open.lim(s, FGb.lim.tag(d))), Wr.err("doc_glob: malformed open")) == False{} : Bool}) -> gom.G(x):
  match d:
    case Wr.Got{t, +r2}:
      match t:
        case 0n:
          gom.none(x, s, r, ex, fs, r2, Wire.wire_nat_exact(r, 0n, r2, ed), other)
        case 1n:
          gom.one(x, s, r, ex, fs, r2, Wire.wire_nat_exact(r, 1n, r2, ed), Wr.get_nat(r2), {==}, other)
        case 2n+y:
          LAWireSpell.ws_absurd(gom.G(x), other)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(gom.G(x), other)

# the skip
def gom.got(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}, other: {String.eq(DocGlob.glob.Snd(FGb.open.got(d)), Wr.err("doc_glob: malformed open")) == False{} : Bool}) -> gom.G(x):
  match d:
    case Wr.Got{+s, +r}:
      +ee = ed
      gom.tag(x, s, r, Wire.wire_nat_exact(x, s, r, ee), Wire.wire_nat_decoded_fits(x, s, r, ee), Wr.get_nat(r), {==}, other)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(gom.G(x), other)

def DocGlob.glob_open_malformed_unless_open(x, other):
  gom.got(x, Wr.get_nat(x), {==}, other)
