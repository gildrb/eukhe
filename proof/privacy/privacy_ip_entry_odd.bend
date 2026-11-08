# eukhe: the proof of LAW privacy_ip_entry_odd
#
# PROOF: the request reads back as the strings spelled
# (wire_strs_round_trip); an odd count of them pairs into nothing
# (pen.pairs_odd), which answers the error form.

import Base
import ../../bend/ffi_privacy.bend as FP
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_strs_round_trip.bend as PWireStrsRoundTrip
import ./base/entry.bend as LEn
import ../../laws/privacy/entry.bend as PrivacyEntry

def PrivacyEntry.privacy_ip_entry_odd(cs, b, fit):
  +xs = List.append(&2, String, PrivacyEntry.cand_strs(cs), [b])
  %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, LawsBase.wire_spell_strs(xs, "")), Wr.Got{xs, ""}, Wire.wire_strs_round_trip(xs, "", fit)) : {FP.ffi.got(_) == Wr.err("privacy: malformed request") : String}
  %Equal.sym(Maybe<&2, List<&2, FP.Cand>>, FP.pairs(xs), None{}, LEn.pen.pairs_odd(cs, b)) : {FP.ffi.end(True{}, _) == Wr.err("privacy: malformed request") : String}
  {==}
