# eukhe: the proof of LAW quirks_open_answers
# The two lists read back (the wire's list round trip), the rules read
# back from their flat list, the entry's compile flag is the model's
# `compiles` (through the spec's verdicts) and its verdicts are spelled as
# the spec spells them.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/quirks.bend as Quirks
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../../laws/base.bend as LawsBase
import ./base.bend as QP

def Quirks.quirks_open_answers(known, rs, fits):
  +ok = fits
  +xs = Quirks.qs_flat(rs)
  +r1 = Wr.put_list(~Nat, ~Wr.put_nat, xs, "")
  +hk = LLogicBool.wr_and_l(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, known)), LawsBase.wire_nats_fit(known)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), ok)
  +hx = LLogicBool.wr_and_r(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, known)), LawsBase.wire_nats_fit(known)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), ok)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, known, r1)), Wr.Got{known, r1}, Wire.wire_list_round_trip(known, r1, hk)) : {FQ.open.known(_) == (Quirks.qs_kept(If.compiles(known, rs), rs), Wr.put_bool(If.compiles(known, rs), Quirks.spell_verdicts(known, rs))) : FQ.St & String}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, r1), Wr.Got{xs, ""}, Wire.wire_list_round_trip(xs, "", hx)) : {FQ.open.rules(known, _) == (Quirks.qs_kept(If.compiles(known, rs), rs), Wr.put_bool(If.compiles(known, rs), Quirks.spell_verdicts(known, rs))) : FQ.St & String}
  %Equal.sym(Maybe<&2, List<&2, If.Rule>>, FQ.rules(xs), Some{rs}, QP.qp.rules(rs)) : {FQ.open.book(known, _) == (Quirks.qs_kept(If.compiles(known, rs), rs), Wr.put_bool(If.compiles(known, rs), Quirks.spell_verdicts(known, rs))) : FQ.St & String}
  +fine = Equal.trans(Bool, If.fine_all(If.verdicts.go(rs, known, 0n)), Quirks.qs_all_fine(rs, known), If.compiles(known, rs), QP.qp.fine_all(rs, known, 0n), QP.qp.all_fine(rs, known))
  %Equal.sym(Bool, If.fine_all(If.verdicts.go(rs, known, 0n)), If.compiles(known, rs), fine) : {FQ.open.reply(_, rs, If.verdicts(known, rs)) == (Quirks.qs_kept(If.compiles(known, rs), rs), Wr.put_bool(If.compiles(known, rs), Quirks.spell_verdicts(known, rs))) : FQ.St & String}
  %QP.qp.verdicts(known, rs) : {FQ.open.reply(If.compiles(known, rs), rs, If.verdicts(known, rs)) == (Quirks.qs_kept(If.compiles(known, rs), rs), Wr.put_bool(If.compiles(known, rs), _)) : FQ.St & String}
  QP.qp.reply(If.compiles(known, rs), rs, If.verdicts(known, rs))
