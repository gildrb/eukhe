# eukhe: the proof of LAW codemode_id_ffi_left_over

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

# PROOF of LAW codemode_id_ffi_left_over: the tag and the text read back with the rest untouched (wire_str_round_trip); the rest is not empty, so the entry answers the left-over error form.

def CodemodeId.codemode_id_ffi_left_over(q, c, t, fit):
  match q:
    case FCi.QId{+n}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(n, SCon{c, t})), Wr.Got{n, SCon{c, t}}, Wire.wire_str_round_trip(n, SCon{c, t}, fit)) : {FCi.ffi.got(FCi.get_id(_)) == Wr.err("codemode_id: input left after the request") : String}
      {==}
    case FCi.QIs{+n}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(n, SCon{c, t})), Wr.Got{n, SCon{c, t}}, Wire.wire_str_round_trip(n, SCon{c, t}, fit)) : {FCi.ffi.got(FCi.get_is(_)) == Wr.err("codemode_id: input left after the request") : String}
      {==}
