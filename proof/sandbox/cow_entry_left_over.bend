# eukhe: the proof of LAW cow_entry_left_over
# The reader reads the three contents back with the input after them;
# that input is not empty, so they are not the whole input (wire_end_exact).

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact
import ./base/cow.bend as LAC

def Sandbox.cow_entry_left_over(p, b, c, hp, hb, hc, more, some):
  %Equal.sym(String, FSb.ffi(Sandbox.cow_spell_req(p, b, c, more)), Sandbox.cow_spec(Sandbox.cow_spell_req(p, b, c, more)), LAC.cse.exact(Sandbox.cow_spell_req(p, b, c, more))) : {_ == Wr.err("sandbox: input left over") : String}
  %LAC.cse.rt_doc(p, Sandbox.cow_spell_doc(b, Sandbox.cow_spell_doc(c, more)), hp) : {Sandbox.cow_spec.p(_) == Wr.err("sandbox: input left over") : String}
  %LAC.cse.rt_doc(b, Sandbox.cow_spell_doc(c, more), hb) : {Sandbox.cow_spec.b(p, _) == Wr.err("sandbox: input left over") : String}
  %LAC.cse.rt_doc(c, more, hc) : {Sandbox.cow_spec.c(p, b, _) == Wr.err("sandbox: input left over") : String}
  %Equal.sym(Bool, Wr.end(more), String.is_empty(more), Wire.wire_end_exact(more)) : {Sandbox.cow_spec.end(_, p, b, c) == Wr.err("sandbox: input left over") : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {Sandbox.cow_spec.end(_, p, b, c) == Wr.err("sandbox: input left over") : String}
  {==}
