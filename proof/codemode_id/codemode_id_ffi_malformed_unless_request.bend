# eukhe: the proof of LAW codemode_id_ffi_malformed_unless_request

import Base
import ../../bend/codemode_id.bend as Ci
import ../../bend/ffi_codemode_id.bend as FCi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../../laws/codemode_id.bend as CodemodeId
import ./base.bend as LACodemodeId

# PROOF of LAW codemode_id_ffi_malformed_unless_request: an answer that is not the malformed error reads a known tag (wire_nat_exact) and a text (wire_str_exact, wire_str_decoded_fits): the input is the spelled request, then the rest after it (ci_mu_top, ci_mu_id, ci_mu_is); every other input answers the malformed error, which the premise excludes.

def CodemodeId.codemode_id_ffi_malformed_unless_request(s, other):
  LACodemodeId.ci_mu_top(s, Wr.get_nat(s), {==}, other)
