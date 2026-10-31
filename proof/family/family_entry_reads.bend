# eukhe: the proof of LAW family_entry_reads
#
# PROOF: each decoder stage answers Got only for the spelling of its value, within the wire (fx.*, from wire_nat_exact, wire_nat_decoded_fits and the list lemmas); a value is answered only for a request read whole (fx.top).

import Base
import ../../bend/family.bend as F
import ../../bend/ffi_family.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/family.bend as Family
import ./base/entry.bend as LE


def Family.family_entry_reads(s, ok):
  LE.fx.top(s, FF.get_req(s), LE.fx.req(s), ok)
