# eukhe: the proof of LAW codemode_id_ffi_answers

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
import ./codemode_id_exact.bend as PCodemodeIdExact

# PROOF of LAW codemode_id_ffi_answers: the tag reads back, the name reads back whole with nothing left (wire_str_round_trip), so the entry answers the model's identifier, which is the spec's (codemode_id_exact).

def CodemodeId.codemode_id_ffi_answers(name, fit):
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(name, "")), Wr.Got{name, ""}, Wire.wire_str_round_trip(name, "", fit)) : {FCi.ffi.got(FCi.get_id(_)) == Wr.put_str(CodemodeId.id_spec(name), "") : String}
  %CodemodeId.codemode_id_exact(name) : {Wr.put_str(Ci.of(name), "") == Wr.put_str(_, "") : String}
  {==}
