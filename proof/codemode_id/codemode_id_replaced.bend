# eukhe: the proof of LAW codemode_id_replaced

import Base
import ../../bend/codemode_id.bend as Ci
import ../../bend/ffi_codemode_id.bend as FCi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../../laws/codemode_id.bend as CodemodeId
import ./base.bend as LACodemodeId

# PROOF of LAW codemode_id_replaced: as codemode_id_kept, the class refusing the char: `_` (ci_start_false, ci_keep_false).

def CodemodeId.codemode_id_replaced(a, x, b, no):
  match a:
    case SNil{}:
      Equal.cong(Char, Maybe<&2, Char>, c => Some{c}, Ci.keep(Ci.start(Chr{x}), Chr{x}), '_', LACodemodeId.ci_keep_false(Ci.start(Chr{x}), Chr{x}, LACodemodeId.ci_start_false(Ci.start(Chr{x}), no)))
    case SCon{h, t}:
      Equal.trans(Maybe<&2, Char>, String.get(Ci.rest(String.append(t, SCon{Chr{x}, b})), String.length(t)), Some{Ci.keep(Ci.part(Chr{x}), Chr{x})}, Some{'_'}, LACodemodeId.ci_rest_get(t, x, b), Equal.cong(Char, Maybe<&2, Char>, c => Some{c}, Ci.keep(Ci.part(Chr{x}), Chr{x}), '_', LACodemodeId.ci_keep_false(Ci.part(Chr{x}), Chr{x}, no)))
