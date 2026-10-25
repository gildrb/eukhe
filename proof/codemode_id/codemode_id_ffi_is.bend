# eukhe: the proof of LAW codemode_id_ffi_is

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
import ./codemode_id_is_exact.bend as PCodemodeIdIsExact

# PROOF of LAW codemode_id_ffi_is: the tag reads back, the text reads back whole with nothing left (wire_str_round_trip), so the entry answers the model's test, which is the spec's (codemode_id_is_exact).

def CodemodeId.codemode_id_ffi_is(text, fit):
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(text, "")), Wr.Got{text, ""}, Wire.wire_str_round_trip(text, "", fit)) : {FCi.ffi.got(FCi.get_is(_)) == Wr.put_bool(CodemodeId.ident_spec(text), "") : String}
  %CodemodeId.codemode_id_is_exact(text) : {Wr.put_bool(Ci.test(text), "") == Wr.put_bool(_, "") : String}
  {==}
