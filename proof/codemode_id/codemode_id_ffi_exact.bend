# eukhe: the proof of LAW codemode_id_ffi_exact

import Base
import ../../bend/codemode_id.bend as Ci
import ../../bend/ffi_codemode_id.bend as FCi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_str_exact.bend as PWireStrExact
import ../base/wire.bend as LWire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../../laws/codemode_id.bend as CodemodeId
import ./base.bend as LACodemodeId

# PROOF of LAW codemode_id_ffi_exact: a reply that is not the error form comes from a known tag (wire_nat_exact) and a decoded text with nothing left (wire_str_exact): the spelled request (ci_ex_top, ci_ex_id, ci_ex_is, ci_sub).

def CodemodeId.codemode_id_ffi_exact(s, ok):
  LACodemodeId.ci_ex_top(s, Wr.get_nat(s), {==}, ok)
