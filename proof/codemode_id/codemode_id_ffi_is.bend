# eukhe: the proof of LAW codemode_id_ffi_is

import Base
import ../../bend/codemode_id.bend as Ci
import ../../bend/ffi_codemode_id.bend as FCi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../../laws/codemode_id.bend as CodemodeId
import ./base.bend as LACodemodeId

# PROOF of LAW codemode_id_ffi_is: the tag reads back, the text reads back whole with nothing left (wire_str_round_trip), so the entry answers the model's test.

def CodemodeId.codemode_id_ffi_is(text, fit):
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(text, "")), Wr.Got{text, ""}, Wire.wire_str_round_trip(text, "", fit)) : {FCi.ffi.got(FCi.get_is(_)) == Wr.put_bool(Ci.test(text), "") : String}
  {==}
