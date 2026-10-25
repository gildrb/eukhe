# eukhe: the proof of LAW codemode_id_ffi_malformed

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

# PROOF of LAW codemode_id_ffi_malformed: each decoder layer that answers Bad, and an unknown tag, reach the malformed error form (ci_bad, ci_bad_id, ci_bad_is).

def CodemodeId.codemode_id_ffi_malformed(s, bad):
  LACodemodeId.ci_bad(Wr.get_nat(s), bad)
