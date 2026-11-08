# eukhe: the proof of LAW rlm_query_entry_malformed_exact
#
# PROOF: every answer opens with a Nat, never 'E' (re.answer_ok); so an answer that opens with 'E' is the one error form (re.refuse).

import Base
import ../../bend/ffi_rlm_query.bend as FRq
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/rlm_query.bend as RlmQuery
import ./base/entry.bend as LE


def RlmQuery.rlm_query_entry_malformed_exact(s, bad):
  LE.re.refuse(FRq.get_req(s), bad)
