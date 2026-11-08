# eukhe: the proof of LAW cow_entry_answers_spelled
# The entry answers as the laws spell; the reader reads back each content
# Rust writes.

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LAC

def Sandbox.cow_entry_answers_spelled(p, b, c, hp, hb, hc):
  %Equal.sym(String, FSb.ffi(Sandbox.cow_spell_req(p, b, c, "")), Sandbox.cow_spec(Sandbox.cow_spell_req(p, b, c, "")), LAC.cse.exact(Sandbox.cow_spell_req(p, b, c, ""))) : {_ == Sandbox.cow_spell_answer(p, b, c) : String}
  %LAC.cse.rt_doc(p, Sandbox.cow_spell_doc(b, Sandbox.cow_spell_doc(c, "")), hp) : {Sandbox.cow_spec.p(_) == Sandbox.cow_spell_answer(p, b, c) : String}
  %LAC.cse.rt_doc(b, Sandbox.cow_spell_doc(c, ""), hb) : {Sandbox.cow_spec.b(p, _) == Sandbox.cow_spell_answer(p, b, c) : String}
  %LAC.cse.rt_doc(c, "", hc) : {Sandbox.cow_spec.c(p, b, _) == Sandbox.cow_spell_answer(p, b, c) : String}
  {==}
