# eukhe: the proof of LAW flagged_excluded

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../bend/autoresearch/stats.bend as ArT
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/log.bend as AgLog

def Autoresearch.flagged_excluded(s):
  match s:
    case ArS.St{c, +seg, mode, +runs, pend}:
      %AgLog.ag.first_unflag(runs, seg) : {AgLog.ag.view(ArS.first(runs, seg), ArS.last(runs, seg), ArT.vals(runs, seg)) == AgLog.ag.view(_, ArS.last(Autoresearch.ar_unflag.rows(runs), seg), ArT.vals(Autoresearch.ar_unflag.rows(runs), seg)) : Maybe<&2, ArD.Dec> & Maybe<&2, ArD.Dec> & Maybe<&2, Nat>}
      %AgLog.ag.last_unflag(runs, seg) : {AgLog.ag.view(ArS.first(runs, seg), ArS.last(runs, seg), ArT.vals(runs, seg)) == AgLog.ag.view(ArS.first(runs, seg), _, ArT.vals(Autoresearch.ar_unflag.rows(runs), seg)) : Maybe<&2, ArD.Dec> & Maybe<&2, ArD.Dec> & Maybe<&2, Nat>}
      %AgLog.ag.vals_unflag(runs, seg) : {AgLog.ag.view(ArS.first(runs, seg), ArS.last(runs, seg), ArT.vals(runs, seg)) == AgLog.ag.view(ArS.first(runs, seg), ArS.last(runs, seg), _) : Maybe<&2, ArD.Dec> & Maybe<&2, ArD.Dec> & Maybe<&2, Nat>}
      {==}
