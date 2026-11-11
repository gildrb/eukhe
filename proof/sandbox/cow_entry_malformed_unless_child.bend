# eukhe: the proof of LAW cow_entry_malformed_unless_child: the entry reads
# the spelled parent and base back (cse.rt_get); the content it reads next
# is spelled and fits (cmu.all); when it reads none the entry answers the
# child's error, which the premise excludes

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/sandbox.bend as Sandbox
import ../wire/base/spell.bend as LAWireSpell
import ./base/cow.bend as LAC

def cmc.Ex(t: String) -> Type:
  &m: Maybe<&2, Nat> -> &rest: String -> ({t == Sandbox.cow_spell_doc(m, rest) : String} & {LawsBase.wire_mfits(m) == True{} : Bool})

def cmc.main(-t: String, -p: Maybe<&2, Nat>, -b: Maybe<&2, Nat>, d: Wr.Dec<Maybe<&2, Nat>>, inv: LAC.cmu(t, d),
  other: {String.eq(FSb.run.c(p, b, d), Wr.err("sandbox: bad child content")) == False{} : Bool}) -> cmc.Ex(t):
  match d:
    case Wr.Got{+m, +r}:
      (m, (r, inv))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cmc.Ex(t), other)

def Sandbox.cow_entry_malformed_unless_child(p, hp, b, hb, t, other):
  cmc.main(t, p, b, FSb.get_doc(t), LAC.cmu.all(t),
    Equal.trans(Bool, String.eq(FSb.run.c(p, b, FSb.get_doc(t)), Wr.err("sandbox: bad child content")), String.eq(FSb.run.b(p, FSb.get_doc(Sandbox.cow_spell_doc(b, t))), Wr.err("sandbox: bad child content")), False{},
      Equal.cong(Wr.Dec<Maybe<&2, Nat>>, Bool, x => String.eq(FSb.run.b(p, x), Wr.err("sandbox: bad child content")), Wr.Got{b, t}, FSb.get_doc(Sandbox.cow_spell_doc(b, t)), LAC.cse.rt_get(b, t, hb)),
      Equal.trans(Bool, String.eq(FSb.run.b(p, FSb.get_doc(Sandbox.cow_spell_doc(b, t))), Wr.err("sandbox: bad child content")), String.eq(FSb.run.p(FSb.get_doc(Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, t)))), Wr.err("sandbox: bad child content")), False{},
        Equal.cong(Wr.Dec<Maybe<&2, Nat>>, Bool, x => String.eq(FSb.run.p(x), Wr.err("sandbox: bad child content")), Wr.Got{p, Sandbox.cow_spell_doc(b, t)}, FSb.get_doc(Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, t))), LAC.cse.rt_get(p, Sandbox.cow_spell_doc(b, t), hp)),
        other)))
