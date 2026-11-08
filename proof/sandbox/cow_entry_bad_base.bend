# eukhe: the proof of LAW cow_entry_bad_base
# The entry reads back the parent's content (cse.rt_get), then the base's
# as the laws' reader does (cse.docs), which the premise says is Bad.

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LAC

def Sandbox.cow_entry_bad_base(p, hp, s, bad):
  %LAC.cse.rt_get(p, s, hp) : {FSb.run.p(_) == Wr.err("sandbox: bad base content") : String}
  %LAC.cse.docs(s) : {FSb.run.b(p, _) == Wr.err("sandbox: bad base content") : String}
  %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Sandbox.cow_read_doc(Wr.get_nat(s)), Wr.Bad{}, bad) : {FSb.run.b(p, _) == Wr.err("sandbox: bad base content") : String}
  {==}
