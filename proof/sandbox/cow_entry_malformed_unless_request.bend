# eukhe: the proof of LAW cow_entry_malformed_unless_request
#
# Each content the entry reads is one the laws spell, and it fits: its tag
# and its id are wire Nats that wire_nat_exact inverts, and a decoded id
# fits (wire_nat_decoded_fits); a tag past 1 is Bad (cmu.all). Threading
# the equation of the input so far through the three contents: when one
# does not read, the entry answers its field's error, which a premise
# excludes; else the three contents and the rest are the witness.

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/sandbox.bend as Sandbox
import ../../laws/wire.bend as Wire
import ../wire/base/spell.bend as LAWireSpell
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits

# what a content decoder answer says about its input s: s spells it, and
# it fits
def cmu(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+m, rest}:
      {s == Sandbox.cow_spell_doc(m, rest) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a content tag 1: its id
def cmu.some(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(1n, s1) : String}, r: Wr.Dec<Nat>, er: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}) -> cmu(s0, FSb.get_doc.some(r)):
  match r:
    case Wr.Got{+x, +s2}:
      +e2 = er
      (Equal.trans(String, s0, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(x, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(x, s2), Wire.wire_nat_exact(s1, x, s2, e2))),
        Wire.wire_nat_decoded_fits(s1, x, s2, e2))
    case Wr.Bad{}:
      Unit{}

def cmu.tag(+s0: String, t: Nat, +s1: String, ex: {s0 == Wr.put_nat(t, s1) : String}) -> cmu(s0, FSb.get_doc.tag(t, s1)):
  match t:
    case 0n:
      (ex, {==})
    case 1n:
      cmu.some(s0, s1, ex, Wr.get_nat(s1), {==})
    case 2n+y:
      Unit{}

def cmu.top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> cmu(s, FSb.get_doc.go(r)):
  match r:
    case Wr.Got{+t, +s1}:
      cmu.tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, er))
    case Wr.Bad{}:
      Unit{}

# every content the entry reads is spelled, and fits
def cmu.all(+s: String) -> cmu(s, FSb.get_doc(s)):
  cmu.top(s, Wr.get_nat(s), {==})

# ---- the entry ----

def cmu.goal(+s: String) -> Type:
  &p: Maybe<&2, Nat> -> &b: Maybe<&2, Nat> -> &c: Maybe<&2, Nat> -> &rest: String -> {(s, Bool.and(LawsBase.wire_mfits(p), Bool.and(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c)))) == (Sandbox.cow_spell_req(p, b, c, rest), True{}) : String & Bool}

def cmu.eq(+s: String, +p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, +rest: String,
  e: {s == Sandbox.cow_spell_req(p, b, c, rest) : String},
  f: {Bool.and(LawsBase.wire_mfits(p), Bool.and(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c))) == True{} : Bool}) -> {(s, Bool.and(LawsBase.wire_mfits(p), Bool.and(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c)))) == (Sandbox.cow_spell_req(p, b, c, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Sandbox.cow_spell_req(p, b, c, rest), e) : {(_, Bool.and(LawsBase.wire_mfits(p), Bool.and(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c)))) == (Sandbox.cow_spell_req(p, b, c, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Bool.and(LawsBase.wire_mfits(p), Bool.and(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c))), True{}, f) : {(Sandbox.cow_spell_req(p, b, c, rest), _) == (Sandbox.cow_spell_req(p, b, c, rest), True{}) : String & Bool}
  {==}

# the child's content: read, it ends the witness; else its error
def cmu.c(+s: String, +p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, -s2: String,
  e: {s == Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, s2)) : String},
  fp: {LawsBase.wire_mfits(p) == True{} : Bool}, fb: {LawsBase.wire_mfits(b) == True{} : Bool},
  d: Wr.Dec<Maybe<&2, Nat>>, inv: cmu(s2, d),
  nc: {String.eq(FSb.run.c(p, b, d), Wr.err("sandbox: bad child content")) == False{} : Bool}) -> cmu.goal(s):
  match d:
    case Wr.Got{+c, +rest}:
      (e3, fc) = inv
      (p, (b, (c, (rest, cmu.eq(s, p, b, c, rest,
        Equal.trans(String, s, Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, s2)), Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, Sandbox.cow_spell_doc(c, rest))), e,
          Equal.cong(String, String, z => Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, z)), s2, Sandbox.cow_spell_doc(c, rest), e3)),
        LAWireSpell.ws_and_tt(LawsBase.wire_mfits(p), Bool.and(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c)), fp,
          LAWireSpell.ws_and_tt(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c), fb, fc)))))))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cmu.goal(s), nc)

# the base's content: read, the child's follows; else its error
def cmu.b(+s: String, +p: Maybe<&2, Nat>, -s1: String,
  e: {s == Sandbox.cow_spell_doc(p, s1) : String},
  fp: {LawsBase.wire_mfits(p) == True{} : Bool},
  d: Wr.Dec<Maybe<&2, Nat>>, inv: cmu(s1, d),
  nb: {String.eq(FSb.run.b(p, d), Wr.err("sandbox: bad base content")) == False{} : Bool},
  nc: {String.eq(FSb.run.b(p, d), Wr.err("sandbox: bad child content")) == False{} : Bool}) -> cmu.goal(s):
  match d:
    case Wr.Got{+b, +s2}:
      (e2, fb) = inv
      cmu.c(s, p, b, s2,
        Equal.trans(String, s, Sandbox.cow_spell_doc(p, s1), Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, s2)), e,
          Equal.cong(String, String, z => Sandbox.cow_spell_doc(p, z), s1, Sandbox.cow_spell_doc(b, s2), e2)),
        fp, fb, FSb.get_doc(s2), cmu.all(s2), nc)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cmu.goal(s), nb)

# the parent's content: read, the base's follows; else its error
def cmu.p(+s: String, d: Wr.Dec<Maybe<&2, Nat>>, inv: cmu(s, d),
  np: {String.eq(FSb.run.p(d), Wr.err("sandbox: bad parent content")) == False{} : Bool},
  nb: {String.eq(FSb.run.p(d), Wr.err("sandbox: bad base content")) == False{} : Bool},
  nc: {String.eq(FSb.run.p(d), Wr.err("sandbox: bad child content")) == False{} : Bool}) -> cmu.goal(s):
  match d:
    case Wr.Got{+p, +s1}:
      (e1, fp) = inv
      cmu.b(s, p, s1, e1, fp, FSb.get_doc(s1), cmu.all(s1), nb, nc)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cmu.goal(s), np)

def Sandbox.cow_entry_malformed_unless_request(s, np, nb, nc):
  cmu.p(s, FSb.get_doc(s), cmu.all(s), np, nb, nc)
