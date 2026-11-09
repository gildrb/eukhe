# eukhe: the proof of LAW cow_entry_left_over
# The entry reads the three contents back with the input after them
# (cse.rt_get); that input is not empty, so they are not the whole input
# (wire_end_exact).

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact
import ./base/cow.bend as LAC

def Sandbox.cow_entry_left_over(p, b, c, hp, hb, hc, more, some):
  %LAC.cse.rt_get(p, Sandbox.cow_spell_doc(b, Sandbox.cow_spell_doc(c, more)), hp) : {FSb.run.p(_) == Wr.err("sandbox: input left over") : String}
  %LAC.cse.rt_get(b, Sandbox.cow_spell_doc(c, more), hb) : {FSb.run.b(p, _) == Wr.err("sandbox: input left over") : String}
  %LAC.cse.rt_get(c, more, hc) : {FSb.run.c(p, b, _) == Wr.err("sandbox: input left over") : String}
  %Equal.sym(Bool, Wr.end(more), String.is_empty(more), Wire.wire_end_exact(more)) : {FSb.run.end(_, p, b, c) == Wr.err("sandbox: input left over") : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {FSb.run.end(_, p, b, c) == Wr.err("sandbox: input left over") : String}
  {==}
