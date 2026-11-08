# eukhe: the proof of LAW cow_entry_bad_child

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LAC

def Sandbox.cow_entry_bad_child(p, hp, b, hb, s, bad):
  %Equal.sym(String, FSb.ffi(Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, s))), Sandbox.cow_spec(Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, s))), LAC.cw.exact(Sandbox.cow_spell_doc(p, Sandbox.cow_spell_doc(b, s)))) : {_ == Wr.err("sandbox: bad child content") : String}
  %LAC.cw.rt_doc(p, Sandbox.cow_spell_doc(b, s), hp) : {Sandbox.cow_spec.p(_) == Wr.err("sandbox: bad child content") : String}
  %LAC.cw.rt_doc(b, s, hb) : {Sandbox.cow_spec.b(p, _) == Wr.err("sandbox: bad child content") : String}
  %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Sandbox.cow_read_doc(Wr.get_nat(s)), Wr.Bad{}, bad) : {Sandbox.cow_spec.c(p, b, _) == Wr.err("sandbox: bad child content") : String}
  {==}
