# eukhe: the proof of LAW err_text_entry_reads_only_requests
#
# PROOF: whatever the decoder reads is the spelling of what it read, then
# its rest, and fits the wire (LA.etb.rp_all, stage by stage with the
# wire's exactness laws); an answer that is no error comes from a request
# read whole, nothing left, and is the spelled spec answer (LA.etb.top).

import Base
import ../../bend/ffi_err_text.bend as FE
import ../../laws/err_text.bend as ErrText
import ./base.bend as LA

def ErrText.err_text_entry_reads_only_requests(s, ok):
  LA.etb.top(s, FE.get_req(s), LA.etb.rp_all(s), ok)
