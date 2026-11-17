# eukhe: the proof of LAW log_stepper_refused_open_history
#
# A refused open leaves the stepper Shut: an open that reads how the
# storage opens and nothing else answers a plan, no error form; every other
# open answers Shut (ph.open). From Shut, induction on the events: each
# answers the refusal and keeps Shut.

import Base
import ../../bend/log.bend as Lr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../base/logic/logic.bend as LLogicLogic

def ph.end(rest: String, h: Lr.How, no: {LawsBase.wire_opens_err(Log.log_reply(FLg.open.end(Wr.end(rest), h))) == True{} : Bool}) -> {Log.log_state(FLg.open.end(Wr.end(rest), h)) == FLg.Shut{} : FLg.St}:
  match rest:
    case SNil{}:
      match h:
        case Lr.Unsynced{}:
          LLogicLogic.wr_absurd({Log.log_state(FLg.open.end(True{}, Lr.Unsynced{})) == FLg.Shut{} : FLg.St}, no)
        case Lr.Synced{}:
          LLogicLogic.wr_absurd({Log.log_state(FLg.open.end(True{}, Lr.Synced{})) == FLg.Shut{} : FLg.St}, no)
        case Lr.Stamped{kept}:
          match kept:
            case True{}:
              LLogicLogic.wr_absurd({Log.log_state(FLg.open.end(True{}, Lr.Stamped{True{}})) == FLg.Shut{} : FLg.St}, no)
            case False{}:
              LLogicLogic.wr_absurd({Log.log_state(FLg.open.end(True{}, Lr.Stamped{False{}})) == FLg.Shut{} : FLg.St}, no)
    case SCon{c, t}:
      {==}

def ph.open(r: Wr.Dec<Lr.How>, no: {LawsBase.wire_opens_err(Log.log_reply(FLg.open.go(r))) == True{} : Bool}) -> {Log.log_state(FLg.open.go(r)) == FLg.Shut{} : FLg.St}:
  match r:
    case Wr.Got{h, rest}:
      ph.end(rest, h, no)
    case Wr.Bad{}:
      {==}

# from Shut, every event answers the refusal
def ph.replies(evs: List<&2, String>) -> {Log.log_replies(evs, FLg.Shut{}) == Log.log_refused(evs) : List<&2, String>}:
  match evs:
    case Nil{}:
      {==}
    case e <> t:
      %ph.replies(t) : {Wr.err("log: the open was refused") <> Log.log_replies(t, FLg.Shut{}) == Wr.err("log: the open was refused") <> _ : List<&2, String>}
      {==}

# from Shut, the stepper stays Shut
def ph.after(evs: List<&2, String>) -> {Log.log_fed_state(evs, FLg.Shut{}) == FLg.Shut{} : FLg.St}:
  match evs:
    case Nil{}:
      {==}
    case e <> t:
      ph.after(t)

def Log.log_stepper_refused_open_history(s, no, evs):
  +st = Log.log_state(FLg.open(s))
  %Equal.sym(FLg.St, st, FLg.Shut{}, ph.open(FLg.get_how(s), no)) : {Log.log_replies(evs, _) == Log.log_refused(evs) : List<&2, String>} & {Log.log_fed_state(evs, _) == FLg.Shut{} : FLg.St}
  (ph.replies(evs), ph.after(evs))
