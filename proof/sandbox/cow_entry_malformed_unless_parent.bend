# eukhe: the proof of LAW cow_entry_malformed_unless_parent: the content
# the entry reads first is spelled and fits (cmu.all); when it reads none
# the entry answers the parent's error, which the premise excludes

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/sandbox.bend as Sandbox
import ../wire/base/spell.bend as LAWireSpell
import ./base/cow.bend as LAC

def cmp.Ex(s: String) -> Type:
  &m: Maybe<&2, Nat> -> &rest: String -> ({s == Sandbox.cow_spell_doc(m, rest) : String} & {LawsBase.wire_mfits(m) == True{} : Bool})

def cmp.main(-s: String, d: Wr.Dec<Maybe<&2, Nat>>, inv: LAC.cmu(s, d),
  other: {String.eq(FSb.run.p(d), Wr.err("sandbox: bad parent content")) == False{} : Bool}) -> cmp.Ex(s):
  match d:
    case Wr.Got{+m, +r}:
      (m, (r, inv))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cmp.Ex(s), other)

def Sandbox.cow_entry_malformed_unless_parent(s, other):
  cmp.main(s, FSb.get_doc(s), LAC.cmu.all(s), other)
