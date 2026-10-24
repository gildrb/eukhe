# eukhe: the proof of LAW log_stepper_open_reads_only_a_bool
#
# A Bool that reads gives the prefix of the input (wire_bool_exact);
# input left over or no Bool answers the error form, which the premise
# refutes.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_bool_exact.bend as PWireBoolExact

def pl.end(rest: String, +s: String, +b: Bool, ex: {s == Wr.put_bool(b, rest) : String}, ok: {LawsBase.wire_opens_err(Log.log_reply(FLg.open.end(Wr.end(rest), b))) == False{} : Bool}) -> &fsync: Bool -> {s == Wr.put_bool(fsync, "") : String}:
  match rest:
    case SNil{}:
      (b, ex)
    case SCon{c, t}:
      LLogicLogic.pt.absurd(&fsync: Bool -> {s == Wr.put_bool(fsync, "") : String}, ok)

def pl.open(+s: String, r: Wr.Dec<Bool>, er: {Wr.get_bool(s) == r : Wr.Dec<Bool>}, ok: {LawsBase.wire_opens_err(Log.log_reply(FLg.open.go(r))) == False{} : Bool}) -> &fsync: Bool -> {s == Wr.put_bool(fsync, "") : String}:
  match r:
    case Wr.Got{+b, +rest}:
      pl.end(rest, s, b, Wire.wire_bool_exact(s, b, rest, er), ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(&fsync: Bool -> {s == Wr.put_bool(fsync, "") : String}, ok)

def Log.log_stepper_open_reads_only_a_bool(s, ok):
  pl.open(s, Wr.get_bool(s), {==}, ok)
