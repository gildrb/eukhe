# eukhe: the proof of LAW codemode_id_keeps_identifiers

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

# PROOF of LAW codemode_id_keeps_identifiers: the premise splits into a first char that may start an identifier and later chars that may continue one (ci_and_both); each is kept (ci_keep_true, ci_rest_keeps).

def CodemodeId.codemode_id_keeps_identifiers(s, ok):
  match s:
    case SNil{}:
      LLogicLogic.absurd({Ci.of(SNil{}) == SNil{} : String}, ok)
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          LACodemodeId.ci_keeps_head(x, t, LACodemodeId.ci_and_both(Bool.or(Ci.start(Chr{x}), False{}), CodemodeId.parts_spec(t), ok))
