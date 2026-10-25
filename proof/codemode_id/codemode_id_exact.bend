# eukhe: the proof of LAW codemode_id_exact

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

# PROOF of LAW codemode_id_exact: induction on the name; after the first char the code's `rest` is the spec's loop with no char read (ci_rest); `keep` is the spec's `fix` (ci_keep_fix); at the first char the spec's digit arm is `and(False, _)`, so its class is the code's `start` (ci_or_false).

def CodemodeId.codemode_id_exact(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          %LACodemodeId.ci_rest(t) : {Ci.of(SCon{Chr{x}, t}) == SCon{CodemodeId.fix_spec(CodemodeId.ok_spec(True{}, x), Chr{x}), _} : String}
          %Equal.sym(Bool, Bool.or(Ci.start(Chr{x}), False{}), Ci.start(Chr{x}), LACodemodeId.ci_or_false(Ci.start(Chr{x}))) : {Ci.of(SCon{Chr{x}, t}) == SCon{CodemodeId.fix_spec(_, Chr{x}), Ci.rest(t)} : String}
          %LACodemodeId.ci_keep_fix(Ci.start(Chr{x}), Chr{x}) : {Ci.of(SCon{Chr{x}, t}) == SCon{_, Ci.rest(t)} : String}
          {==}
