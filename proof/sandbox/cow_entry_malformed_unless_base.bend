# eukhe: the proof of LAW cow_entry_malformed_unless_base: the entry reads
# the spelled parent back (cse.rt_get); the content it reads next is
# spelled and fits (cmu.all); when it reads none the entry answers the
# base's error, which the premise excludes

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/sandbox.bend as Sandbox
import ../wire/base/spell.bend as LAWireSpell
import ./base/cow.bend as LAC

def cmb.Ex(t: String) -> Type:
  &m: Maybe<&2, Nat> -> &rest: String -> ({t == Sandbox.cow_spell_doc(m, rest) : String} & {LawsBase.wire_mfits(m) == True{} : Bool})

def cmb.main(-t: String, -p: Maybe<&2, Nat>, d: Wr.Dec<Maybe<&2, Nat>>, inv: LAC.cmu(t, d),
  other: {String.eq(FSb.run.b(p, d), Wr.err("sandbox: bad base content")) == False{} : Bool}) -> cmb.Ex(t):
  match d:
    case Wr.Got{+m, +r}:
      (m, (r, inv))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cmb.Ex(t), other)

def Sandbox.cow_entry_malformed_unless_base(p, hp, t, other):
  cmb.main(t, p, FSb.get_doc(t), LAC.cmu.all(t),
    Equal.trans(Bool, String.eq(FSb.run.b(p, FSb.get_doc(t)), Wr.err("sandbox: bad base content")), String.eq(FSb.run.p(FSb.get_doc(Sandbox.cow_spell_doc(p, t))), Wr.err("sandbox: bad base content")), False{},
      Equal.cong(Wr.Dec<Maybe<&2, Nat>>, Bool, x => String.eq(FSb.run.p(x), Wr.err("sandbox: bad base content")), Wr.Got{p, t}, FSb.get_doc(Sandbox.cow_spell_doc(p, t)), LAC.cse.rt_get(p, t, hp)),
      other))
