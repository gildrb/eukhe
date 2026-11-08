# eukhe: the proof of LAW rlm_query_entry_reads
#
# PROOF: each decoder stage answers Got only for the spelling of what it read, within the wire (re.x.*, from wire_nat_exact, wire_nat_decoded_fits, wire_list_exact with re.nats_fit, and the string lemma dcw.str); a value is answered only for a request read whole (re.top).

import Base
import ../../bend/ffi_rlm_query.bend as FRq
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/rlm_query.bend as RlmQuery
import ./base/entry.bend as LE


def RlmQuery.rlm_query_entry_reads(s, ok):
  LE.re.top(s, FRq.get_req(s), LE.re.x.req(s), ok)
