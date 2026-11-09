# eukhe: the proof of LAW log_stepper_refused_open_history
#
# A refused open leaves the stepper Shut (LAW log_stepper_open_refused_shuts);
# from Shut, induction on the events: each answers the refusal and keeps
# Shut.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/log.bend as Log
import ./log_stepper_open_refused_shuts.bend as PShuts

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
  %Equal.sym(FLg.St, st, FLg.Shut{}, Log.log_stepper_open_refused_shuts(s, no)) : {Log.log_replies(evs, _) == Log.log_refused(evs) : List<&2, String>} & {Log.log_fed_state(evs, _) == FLg.Shut{} : FLg.St}
  (ph.replies(evs), ph.after(evs))
