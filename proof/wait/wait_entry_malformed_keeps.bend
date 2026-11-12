# eukhe: the proof of LAW wait_entry_malformed_keeps
# A poll read whole answers a spelled list of ends, never an error form
# (LA.wr.ends_ok); nothing read, or a rest that is not empty, keeps the
# wait and answers the malformed-poll error.

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

def mk.fin(+w: Wt.W, +r: Wt.Polled, rest: String, bad: {LawsBase.wire_opens_err(WaitLaws.ww_reply(FWt.step.end(Wr.end(rest), w, r))) == True{} : Bool}) -> {FWt.step.end(Wr.end(rest), w, r) == (FWt.Live{w}, WaitLaws.ww_bad_poll()) : FWt.St & String}:
  match rest:
    case SNil{}:
      +es = Wt.go(Wt.sigs(r), w)
      LA.pw.absurd({FWt.step.end(True{}, w, r) == (FWt.Live{w}, WaitLaws.ww_bad_poll()) : FWt.St & String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FWt.put_ends(es)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FWt.put_ends(es)), True{}, bad), LA.wr.ends_ok(es)))
    case SCon{h, t}:
      {==}

def mk.main(+w: Wt.W, d: Wr.Dec<Wt.Polled>, bad: {LawsBase.wire_opens_err(WaitLaws.ww_reply(FWt.step.poll(w, d))) == True{} : Bool}) -> {FWt.step.poll(w, d) == (FWt.Live{w}, WaitLaws.ww_bad_poll()) : FWt.St & String}:
  match d:
    case Wr.Got{+r, +rest}:
      mk.fin(w, r, rest, bad)
    case Wr.Bad{}:
      {==}

def WaitLaws.wait_entry_malformed_keeps(w, s, bad):
  mk.main(w, FWt.get_ready(s), bad)
