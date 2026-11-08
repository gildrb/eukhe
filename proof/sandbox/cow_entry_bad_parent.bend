# eukhe: the proof of LAW cow_entry_bad_parent

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LAC

def Sandbox.cow_entry_bad_parent(s, bad):
  %Equal.sym(String, FSb.ffi(s), Sandbox.cow_spec(s), LAC.cse.exact(s)) : {_ == Wr.err("sandbox: bad parent content") : String}
  %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Sandbox.cow_read_doc(Wr.get_nat(s)), Wr.Bad{}, bad) : {Sandbox.cow_spec.p(_) == Wr.err("sandbox: bad parent content") : String}
  {==}
