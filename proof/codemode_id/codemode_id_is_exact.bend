# eukhe: the proof of LAW codemode_id_is_exact

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

# PROOF of LAW codemode_id_is_exact: induction on the text: the code's `parts` is the spec's (ci_parts_eq); at the first char the spec's digit arm is `and(False, _)` (ci_or_false).

def CodemodeId.codemode_id_is_exact(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          %LACodemodeId.ci_parts_eq(t) : {Bool.and(Ci.start(Chr{x}), Ci.parts(t)) == Bool.and(Bool.or(Ci.start(Chr{x}), False{}), _) : Bool}
          %Equal.sym(Bool, Bool.or(Ci.start(Chr{x}), False{}), Ci.start(Chr{x}), LACodemodeId.ci_or_false(Ci.start(Chr{x}))) : {Bool.and(Ci.start(Chr{x}), Ci.parts(t)) == Bool.and(_, Ci.parts(t)) : Bool}
          {==}
