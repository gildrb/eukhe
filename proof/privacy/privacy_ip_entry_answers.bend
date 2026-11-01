# eukhe: the proof of LAW privacy_ip_entry_answers
#
# PROOF: the request reads back as the strings spelled
# (wire_strs_round_trip), which pair back into the candidates (pen.pairs);
# the entry's answers are the laws' (pen.answers).

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../bend/ffi_privacy.bend as FP
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_strs_round_trip.bend as PWireStrsRoundTrip
import ./base/entry.bend as LEn
import ../../laws/privacy/entry.bend as PrivacyEntry

def PrivacyEntry.privacy_ip_entry_answers(cs, fit):
  %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, LawsBase.wire_spell_strs(PrivacyEntry.cand_strs(cs), "")), Wr.Got{PrivacyEntry.cand_strs(cs), ""}, Wire.wire_strs_round_trip(PrivacyEntry.cand_strs(cs), "", fit)) : {FP.ffi.got(_) == PrivacyEntry.spell_answers(cs) : String}
  %Equal.sym(Maybe<&2, List<&2, FP.Cand>>, FP.pairs(PrivacyEntry.cand_strs(cs)), Some{cs}, LEn.pen.pairs(cs)) : {FP.ffi.end(True{}, _) == PrivacyEntry.spell_answers(cs) : String}
  %Equal.sym(List<&2, Nat>, FP.answers(cs), PrivacyEntry.answers(cs), LEn.pen.answers(cs)) : {Wr.put_list(~Nat, ~Wr.put_nat, _, "") == PrivacyEntry.spell_answers(cs) : String}
  {==}
