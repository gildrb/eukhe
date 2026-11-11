# eukhe: the proof of LAW codemode_id_is_of

import Base
import ../../bend/codemode_id.bend as Ci
import ../../bend/ffi_codemode_id.bend as FCi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../../laws/codemode_id.bend as CodemodeId
import ./base.bend as LACodemodeId

# PROOF of LAW codemode_id_is_of: the empty text is no identifier on both sides; else the first char is kept exactly when it may start one, and then the identifier is the text exactly when every later char may continue one (ci_test_step, ci_rest_eq): a replaced char is `_`, which differs from the char it replaced, since `_` is in every class (ci_eq_under, ci_not_under).

def CodemodeId.codemode_id_is_of(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          LACodemodeId.ci_test_step(Ci.start(Chr{x}), x, t, {==})
