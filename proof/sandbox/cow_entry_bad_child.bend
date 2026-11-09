# eukhe: the proof of LAW cow_entry_bad_child
# The entry reads back the parent's and the base's contents (cse.rt_get),
# then the child's as the laws' reader does (cse.docs), which the premise
# says is Bad.

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LAC

def Sandbox.cow_entry_bad_child(p, hp, b, hb, s, bad):
  %LAC.cse.rt_get(p, Sandbox.cow_spell_doc(b, s), hp) : {FSb.run.p(_) == Wr.err("sandbox: bad child content") : String}
  %LAC.cse.rt_get(b, s, hb) : {FSb.run.b(p, _) == Wr.err("sandbox: bad child content") : String}
  %LAC.cse.docs(s) : {FSb.run.c(p, b, _) == Wr.err("sandbox: bad child content") : String}
  %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Sandbox.cow_read_doc(Wr.get_nat(s)), Wr.Bad{}, bad) : {FSb.run.c(p, b, _) == Wr.err("sandbox: bad child content") : String}
  {==}
