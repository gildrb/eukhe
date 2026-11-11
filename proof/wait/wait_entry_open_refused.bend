# eukhe: the proof of LAW wait_entry_open_refused
# A deadline read whole answers a spelled list of ends (each of the three
# shapes of a deadline computes), never an error form; nothing read, or a
# rest that is not empty, opens the refused state with the malformed-open
# error.

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

def rf.whole(dl: Maybe<&2, Nat>, bad: {LawsBase.wire_opens_err(WaitLaws.ww_reply(FWt.open.end(True{}, dl))) == True{} : Bool}) -> {FWt.open.end(True{}, dl) == (FWt.Shut{}, WaitLaws.ww_bad_open()) : FWt.St & String}:
  match dl:
    case None{}:
      LA.pw.absurd({FWt.open.end(True{}, None{}) == (FWt.Shut{}, WaitLaws.ww_bad_open()) : FWt.St & String}, Equal.sym(Bool, False{}, True{}, bad))
    case Some{d}:
      match d:
        case 0n:
          LA.pw.absurd({FWt.open.end(True{}, Some{0n}) == (FWt.Shut{}, WaitLaws.ww_bad_open()) : FWt.St & String}, Equal.sym(Bool, False{}, True{}, bad))
        case 1n+m:
          LA.pw.absurd({FWt.open.end(True{}, Some{1n+m}) == (FWt.Shut{}, WaitLaws.ww_bad_open()) : FWt.St & String}, Equal.sym(Bool, False{}, True{}, bad))

def rf.fin(+dl: Maybe<&2, Nat>, rest: String, bad: {LawsBase.wire_opens_err(WaitLaws.ww_reply(FWt.open.end(Wr.end(rest), dl))) == True{} : Bool}) -> {FWt.open.end(Wr.end(rest), dl) == (FWt.Shut{}, WaitLaws.ww_bad_open()) : FWt.St & String}:
  match rest:
    case SNil{}:
      rf.whole(dl, bad)
    case SCon{h, t}:
      {==}

def rf.main(d: Wr.Dec<Maybe<&2, Nat>>, bad: {LawsBase.wire_opens_err(WaitLaws.ww_reply(FWt.open.dl(d))) == True{} : Bool}) -> {FWt.open.dl(d) == (FWt.Shut{}, WaitLaws.ww_bad_open()) : FWt.St & String}:
  match d:
    case Wr.Got{+dl, +rest}:
      rf.fin(dl, rest, bad)
    case Wr.Bad{}:
      {==}

def WaitLaws.wait_entry_open_refused(s, bad):
  rf.main(FWt.get_dl(s), bad)
