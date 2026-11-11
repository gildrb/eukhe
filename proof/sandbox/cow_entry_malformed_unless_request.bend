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
import ../wire/base/spell.bend as LAWireSpell
import ./base/cow.bend as LAC

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
  d: Wr.Dec<Maybe<&2, Nat>>, inv: LAC.cmu(s2, d),
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
  d: Wr.Dec<Maybe<&2, Nat>>, inv: LAC.cmu(s1, d),
  nb: {String.eq(FSb.run.b(p, d), Wr.err("sandbox: bad base content")) == False{} : Bool},
  nc: {String.eq(FSb.run.b(p, d), Wr.err("sandbox: bad child content")) == False{} : Bool}) -> cmu.goal(s):
  match d:
    case Wr.Got{+b, +s2}:
      (e2, fb) = inv
      cmu.c(s, p, b, s2,
        Equal.trans(String, s, Sandbox.cow_spell_doc(p, s1), Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, s2)), e,
          Equal.cong(String, String, z => Sandbox.cow_spell_doc(p, z), s1, Sandbox.cow_spell_doc(b, s2), e2)),
        fp, fb, FSb.get_doc(s2), LAC.cmu.all(s2), nc)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cmu.goal(s), nb)

# the parent's content: read, the base's follows; else its error
def cmu.p(+s: String, d: Wr.Dec<Maybe<&2, Nat>>, inv: LAC.cmu(s, d),
  np: {String.eq(FSb.run.p(d), Wr.err("sandbox: bad parent content")) == False{} : Bool},
  nb: {String.eq(FSb.run.p(d), Wr.err("sandbox: bad base content")) == False{} : Bool},
  nc: {String.eq(FSb.run.p(d), Wr.err("sandbox: bad child content")) == False{} : Bool}) -> cmu.goal(s):
  match d:
    case Wr.Got{+p, +s1}:
      (e1, fp) = inv
      cmu.b(s, p, s1, e1, fp, FSb.get_doc(s1), LAC.cmu.all(s1), nb, nc)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cmu.goal(s), np)

def Sandbox.cow_entry_malformed_unless_request(s, np, nb, nc):
  cmu.p(s, FSb.get_doc(s), LAC.cmu.all(s), np, nb, nc)
