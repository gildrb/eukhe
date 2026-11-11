# eukhe: the proof of LAW codemode_id_length

import Base
import ../../bend/codemode_id.bend as Ci
import ../../bend/ffi_codemode_id.bend as FCi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../../laws/codemode_id.bend as CodemodeId
import ./base.bend as LACodemodeId

# PROOF of LAW codemode_id_length: the first char becomes one char; the later chars keep their count (ci_len_rest).

def CodemodeId.codemode_id_length(c, t):
  Equal.cong(Nat, Nat, n => 1n+n, String.length(Ci.rest(t)), String.length(t), LACodemodeId.ci_len_rest(t))
