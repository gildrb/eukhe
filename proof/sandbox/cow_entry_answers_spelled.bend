# eukhe: the proof of LAW cow_entry_answers_spelled
# The entry reads back each content Rust writes (cse.rt_get), finds no
# input left, and spells the plan as the laws do (cse.plan).

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/sandbox.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LAC

def Sandbox.cow_entry_answers_spelled(p, b, c, hp, hb, hc):
  %LAC.cse.rt_get(p, Sandbox.cow_spell_doc(b, Sandbox.cow_spell_doc(c, "")), hp) : {FSb.run.p(_) == Sandbox.cow_spell_answer(p, b, c) : String}
  %LAC.cse.rt_get(b, Sandbox.cow_spell_doc(c, ""), hb) : {FSb.run.b(p, _) == Sandbox.cow_spell_answer(p, b, c) : String}
  %LAC.cse.rt_get(c, "", hc) : {FSb.run.c(p, b, _) == Sandbox.cow_spell_answer(p, b, c) : String}
  LAC.cse.plan(Sb.plan(p, b, c))
