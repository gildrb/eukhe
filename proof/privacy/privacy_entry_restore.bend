# eukhe: the proof of LAW privacy_entry_restore
#
# PROOF: the event reads back: its tag (wire_nat_round_trip), its classes
# and its indexes (wire_nats_spells, wire_list_round_trip; every tag fits,
# pen.refs_tags_fit, pen.refs_idx_fit), zipped back into the tokens
# (pen.zip_refs); the entry spells the values found as the laws do
# (pen.found).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../bend/ffi_privacy.bend as FP
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ../base/wire.bend as PBaseWire
import ./base/chars.bend as LIp
import ./base/entry.bend as LEn
import ../../laws/privacy/entry.bend as PrivacyEntry

def PrivacyEntry.privacy_entry_restore(b, rs, fit):
  +T = PrivacyEntry.ref_tags(rs)
  +I = PrivacyEntry.ref_indexes(rs)
  +Y = LawsBase.wire_spell_nats(I, "")
  +F = Tk.restore_toks(rs, b)
  +hl = LIp.pip.and_l(LawsBase.wire_fits(List.length(&2, Tk.Ref, rs)), LawsBase.wire_nats_fit(I), fit)
  +hi = LIp.pip.and_r(LawsBase.wire_fits(List.length(&2, Tk.Ref, rs)), LawsBase.wire_nats_fit(I), fit)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, LawsBase.wire_spell_nats(T, Y))), Wr.Got{1n, LawsBase.wire_spell_nats(T, Y)}, Wire.wire_nat_round_trip(1n, LawsBase.wire_spell_nats(T, Y), {==})) : {FP.step.ev(b, FP.get_ev.tag(_)) == (FP.Live{b}, PrivacyEntry.spell_found(F)) : FP.St & String}
  %Wire.wire_nats_spells(T, Y) : {FP.step.ev(b, FP.get_restore(Wr.get_list(~Nat, ~Wr.get_nat, _))) == (FP.Live{b}, PrivacyEntry.spell_found(F)) : FP.St & String}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, T, Y)), Wr.Got{T, Y}, Wire.wire_list_round_trip(T, Y, LEn.pen.refs_tags_fit(rs, hl))) : {FP.step.ev(b, FP.get_restore(_)) == (FP.Live{b}, PrivacyEntry.spell_found(F)) : FP.St & String}
  %Wire.wire_nats_spells(I, "") : {FP.step.ev(b, FP.get_restore.refs(T, Wr.get_list(~Nat, ~Wr.get_nat, _))) == (FP.Live{b}, PrivacyEntry.spell_found(F)) : FP.St & String}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, I, "")), Wr.Got{I, ""}, Wire.wire_list_round_trip(I, "", LEn.pen.refs_idx_fit(rs, hl, hi))) : {FP.step.ev(b, FP.get_restore.refs(T, _)) == (FP.Live{b}, PrivacyEntry.spell_found(F)) : FP.St & String}
  %Equal.sym(Maybe<&2, List<&2, Tk.Ref>>, FP.zip_refs(T, I), Some{rs}, LEn.pen.zip_refs(rs)) : {FP.step.ev(b, FP.ev.of(FP.restore.of(_), "")) == (FP.Live{b}, PrivacyEntry.spell_found(F)) : FP.St & String}
  %Equal.sym(String, FP.put_found.items(F, ""), PrivacyEntry.found_items(F), LEn.pen.found(F)) : {(FP.Live{b}, Wr.put_nat(List.length(&2, Maybe<&2, String>, F), _)) == (FP.Live{b}, PrivacyEntry.spell_found(F)) : FP.St & String}
  {==}
