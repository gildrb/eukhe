# eukhe: the proof of LAW log_stepper_open_refused_shuts
#
# An open that reads its Bool and nothing else answers a plan, no error
# form; every other open answers Shut.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../base/logic/logic.bend as LLogicLogic

def pl.end(rest: String, b: Bool, no: {LawsBase.wire_opens_err(Log.log_reply(FLg.open.end(Wr.end(rest), b))) == True{} : Bool}) -> {Log.log_state(FLg.open.end(Wr.end(rest), b)) == FLg.Shut{} : FLg.St}:
  match rest:
    case SNil{}:
      match b:
        case True{}:
          LLogicLogic.wr_absurd({Log.log_state(FLg.open.end(True{}, True{})) == FLg.Shut{} : FLg.St}, no)
        case False{}:
          LLogicLogic.wr_absurd({Log.log_state(FLg.open.end(True{}, False{})) == FLg.Shut{} : FLg.St}, no)
    case SCon{c, t}:
      {==}

def pl.open(r: Wr.Dec<Bool>, no: {LawsBase.wire_opens_err(Log.log_reply(FLg.open.go(r))) == True{} : Bool}) -> {Log.log_state(FLg.open.go(r)) == FLg.Shut{} : FLg.St}:
  match r:
    case Wr.Got{b, rest}:
      pl.end(rest, b, no)
    case Wr.Bad{}:
      {==}

def Log.log_stepper_open_refused_shuts(s, no):
  pl.open(Wr.get_bool(s), no)
