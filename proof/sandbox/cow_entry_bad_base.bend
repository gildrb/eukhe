# eukhe: the proof of LAW cow_entry_bad_base

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LAC

def Sandbox.cow_entry_bad_base(p, hp, s, bad):
  %Equal.sym(String, FSb.ffi(Sandbox.cow_spell_doc(p, s)), Sandbox.cow_spec(Sandbox.cow_spell_doc(p, s)), LAC.cse.exact(Sandbox.cow_spell_doc(p, s))) : {_ == Wr.err("sandbox: bad base content") : String}
  %LAC.cse.rt_doc(p, s, hp) : {Sandbox.cow_spec.p(_) == Wr.err("sandbox: bad base content") : String}
  %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Sandbox.cow_read_doc(Wr.get_nat(s)), Wr.Bad{}, bad) : {Sandbox.cow_spec.b(p, _) == Wr.err("sandbox: bad base content") : String}
  {==}
