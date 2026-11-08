# eukhe: the proof of LAW log_stepper_open_malformed_unless_bool
#
# A Bool that reads gives the prefix of the input (wire_bool_exact); no
# Bool answers the malformed open, which the premise refutes.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/log.bend as Log
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_bool_exact.bend as PWireBoolExact

def lob.G(+s: String) -> Type:
  &fsync: Bool -> &rest: String -> {s == Wr.put_bool(fsync, rest) : String}

def lob.open(+s: String, r: Wr.Dec<Bool>, er: {Wr.get_bool(s) == r : Wr.Dec<Bool>}, other: {String.eq(Log.log_reply(FLg.open.go(r)), Wr.err("log: malformed open")) == False{} : Bool}) -> lob.G(s):
  match r:
    case Wr.Got{+b, +rest}:
      (b, (rest, Wire.wire_bool_exact(s, b, rest, er)))
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(lob.G(s), other)

def Log.log_stepper_open_malformed_unless_bool(s, other):
  lob.open(s, Wr.get_bool(s), {==}, other)
