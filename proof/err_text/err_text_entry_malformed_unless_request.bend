# eukhe: the proof of LAW err_text_entry_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (LA.etb.rp_all); when it reads none the entry answers the
# malformed error, which the premise excludes (LA.etb.mu).

import Base
import ../../bend/ffi_err_text.bend as FE
import ../../laws/err_text.bend as ErrText
import ./base.bend as LA

def ErrText.err_text_entry_malformed_unless_request(s, other):
  LA.etb.mu(s, FE.get_req(s), LA.etb.rp_all(s), other)
