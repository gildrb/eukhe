# eukhe: the proof of LAW codemode_id_is_identifier

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

# PROOF of LAW codemode_id_is_identifier: split on whether the first char may start an identifier (ci_head_at): kept, its class is True; replaced, `_` may start one; every later char, kept or `_`, may continue one (ci_parts, ci_parts_at).

def CodemodeId.codemode_id_is_identifier(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          LACodemodeId.ci_head_at(Ci.start(Chr{x}), x, {==}, t)
