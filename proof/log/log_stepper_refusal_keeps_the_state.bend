# eukhe: the proof of LAW log_stepper_refusal_keeps_the_state
#
# A step that reads a commit answers a plan, never the error form
# (pe.reply_ok); every refused step answers the state it was given.

import Base
import ../../bend/log.bend as Lr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def pl.end(rest: String, +x: Lr.Store, +ds: List<&2, Bool>, no: {LawsBase.wire_opens_err(Log.log_reply(FLg.step.end(Wr.end(rest), x, ds))) == True{} : Bool}) -> {Log.log_state(FLg.step.end(Wr.end(rest), x, ds)) == FLg.Running{x} : FLg.St}:
  match rest:
    case SNil{}:
      +p = Lr.Store.commit(x, ds)
      +e = LawsBase.wire_opens_err(Log.log_reply(FLg.reply(p)))
      LLogicLogic.wr_absurd({Log.log_state(FLg.reply(p)) == FLg.Running{x} : FLg.St}, Equal.trans(Bool, False{}, e, True{}, Equal.sym(Bool, e, False{}, LA.pe.reply_ok(p)), no))
    case SCon{c, t}:
      {==}

def pl.step(+x: Lr.Store, r: Wr.Dec<List<&2, Bool>>, no: {LawsBase.wire_opens_err(Log.log_reply(FLg.step.go(x, r))) == True{} : Bool}) -> {Log.log_state(FLg.step.go(x, r)) == FLg.Running{x} : FLg.St}:
  match r:
    case Wr.Got{ds, rest}:
      pl.end(rest, x, ds, no)
    case Wr.Bad{}:
      {==}

def Log.log_stepper_refusal_keeps_the_state(st, s, no):
  match st:
    case FLg.Running{+x}:
      pl.step(x, Wr.get_list(~Bool, ~Wr.get_bool, s), no)
    case FLg.Shut{}:
      {==}
