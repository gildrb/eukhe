# eukhe: the proof of LAW cow_entry_bad_parent
# The entry reads the parent's content as the laws' reader does
# (cse.docs), which the premise says is Bad.

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LAC

def Sandbox.cow_entry_bad_parent(s, bad):
  %LAC.cse.docs(s) : {FSb.run.p(_) == Wr.err("sandbox: bad parent content") : String}
  %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Sandbox.cow_read_doc(Wr.get_nat(s)), Wr.Bad{}, bad) : {FSb.run.p(_) == Wr.err("sandbox: bad parent content") : String}
  {==}
