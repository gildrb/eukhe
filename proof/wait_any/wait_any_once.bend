# eukhe: the proof of LAW wait_any_once
#
# PROOF: no events deliver more than what is left (wa.once_go): one for a
# running or kept job, none for a sent one, and none is at most one
# (wa.le01).

import Base
import ../../bend/wait_any.bend as Wa
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW

def WaitAny.wait_any_once(wake, es, d):
  match d:
    case Wa.D{+w, p}:
      match p:
        case Wa.Live{}:
          LW.wa.once_go(es, wake, Wa.D{w, Wa.Live{}})
        case Wa.Kept{}:
          LW.wa.once_go(es, wake, Wa.D{w, Wa.Kept{}})
        case Wa.Sent{}:
          LW.wa.le01(WaitAny.wa_count(es, wake, Wa.D{w, Wa.Sent{}}), LW.wa.once_go(es, wake, Wa.D{w, Wa.Sent{}}))
