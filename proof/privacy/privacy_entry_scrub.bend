# eukhe: the proof of LAW privacy_entry_scrub
#
# PROOF: the event reads back: its tag (wire_nat_round_trip), its classes
# (wire_nats_spells, wire_list_round_trip; every tag fits, pen.vals_tags_fit),
# its values (wire_strs_round_trip), zipped back into the values
# (pen.zip_vals); the entry's reply to them is the laws' (pen.reply).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../bend/ffi_privacy.bend as FP
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_strs_round_trip.bend as PWireStrsRoundTrip
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ../base/wire.bend as PBaseWire
import ./base/chars.bend as LIp
import ./base/entry.bend as LEn
import ../../laws/privacy/entry.bend as PrivacyEntry

def PrivacyEntry.privacy_entry_scrub(b, vs, fit):
  +T = PrivacyEntry.val_tags(vs)
  +X = PrivacyEntry.val_texts(vs)
  +Y = LawsBase.wire_spell_strs(X, "")
  +hl = LIp.pip.and_l(LawsBase.wire_fits(List.length(&2, Tk.Val, vs)), LawsBase.wire_strs_fit(X), fit)
  +hx = LIp.pip.and_r(LawsBase.wire_fits(List.length(&2, Tk.Val, vs)), LawsBase.wire_strs_fit(X), fit)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, LawsBase.wire_spell_nats(T, Y))), Wr.Got{0n, LawsBase.wire_spell_nats(T, Y)}, Wire.wire_nat_round_trip(0n, LawsBase.wire_spell_nats(T, Y), {==})) : {FP.step.ev(b, FP.get_ev.tag(_)) == PrivacyEntry.scrub_reply(Tk.scrub_vals(vs, b)) : FP.St & String}
  %Wire.wire_nats_spells(T, Y) : {FP.step.ev(b, FP.get_scrub(Wr.get_list(~Nat, ~Wr.get_nat, _))) == PrivacyEntry.scrub_reply(Tk.scrub_vals(vs, b)) : FP.St & String}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, T, Y)), Wr.Got{T, Y}, Wire.wire_list_round_trip(T, Y, LEn.pen.vals_tags_fit(vs, hl))) : {FP.step.ev(b, FP.get_scrub(_)) == PrivacyEntry.scrub_reply(Tk.scrub_vals(vs, b)) : FP.St & String}
  %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, Y), Wr.Got{X, ""}, Wire.wire_strs_round_trip(X, "", hx)) : {FP.step.ev(b, FP.get_scrub.vals(T, _)) == PrivacyEntry.scrub_reply(Tk.scrub_vals(vs, b)) : FP.St & String}
  %Equal.sym(Maybe<&2, List<&2, Tk.Val>>, FP.zip_vals(T, X), Some{vs}, LEn.pen.zip_vals(vs)) : {FP.step.ev(b, FP.ev.of(FP.scrub.of(_), "")) == PrivacyEntry.scrub_reply(Tk.scrub_vals(vs, b)) : FP.St & String}
  LEn.pen.reply(Tk.scrub_vals(vs, b))
