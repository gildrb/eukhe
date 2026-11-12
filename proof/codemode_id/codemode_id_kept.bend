# eukhe: the proof of LAW codemode_id_kept

import Base
import ../../bend/codemode_id.bend as Ci
import ../../bend/ffi_codemode_id.bend as FCi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../../laws/codemode_id.bend as CodemodeId
import ./base.bend as LACodemodeId

# PROOF of LAW codemode_id_kept: with nothing before it the char is the first, kept by its start class (ci_start_true, ci_keep_true); after a char it is a later char at the same place (ci_rest_get), kept by its continue class.

def CodemodeId.codemode_id_kept(a, x, b, ok):
  match a:
    case SNil{}:
      Equal.cong(Char, Maybe<&2, Char>, c => Some{c}, Ci.keep(Ci.start(Chr{x}), Chr{x}), Chr{x}, LACodemodeId.ci_keep_true(Ci.start(Chr{x}), Chr{x}, LACodemodeId.ci_start_true(Ci.start(Chr{x}), ok)))
    case SCon{h, t}:
      Equal.trans(Maybe<&2, Char>, String.get(Ci.rest(String.append(t, SCon{Chr{x}, b})), String.length(t)), Some{Ci.keep(Ci.part(Chr{x}), Chr{x})}, Some{Chr{x}}, LACodemodeId.ci_rest_get(t, x, b), Equal.cong(Char, Maybe<&2, Char>, c => Some{c}, Ci.keep(Ci.part(Chr{x}), Chr{x}), Chr{x}, LACodemodeId.ci_keep_true(Ci.part(Chr{x}), Chr{x}, ok)))
