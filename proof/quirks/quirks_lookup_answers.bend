# eukhe: the proof of LAW quirks_lookup_answers
# The four Nats read back (the wire's list round trip); the entry then
# answers the model's lookup, spelled as the spec spells it.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/quirks.bend as Quirks
import ../../laws/wire.bend as Wire
import ./base.bend as QP

def Quirks.quirks_lookup_answers(rs, q, d, fits):
  match q:
    case If.Query{+f, +m, +h}:
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, [f, m, h, d], "")), Wr.Got{[f, m, h, d], ""}, Wire.wire_list_round_trip([f, m, h, d], "", fits)) : {FQ.step.book(rs, _) == (FQ.Book{rs}, Quirks.spell_ans(If.lookup(rs, If.Query{f, m, h}, d))) : FQ.St & String}
      %QP.qp.ans(If.lookup(rs, If.Query{f, m, h}, d)) : {FQ.step.book(rs, Wr.Got{[f, m, h, d], ""}) == (FQ.Book{rs}, _) : FQ.St & String}
      {==}
