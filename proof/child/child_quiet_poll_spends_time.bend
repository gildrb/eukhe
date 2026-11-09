# eukhe: the proof of LAW child_quiet_poll_spends_time
#
# PROOF: the held token is no news (moved_self), so the poll spends the
# elapsed ms off the clock (LA.pc.spends).

import Base
import ../../bend/child.bend as Ch
import ../../spec/child.bend as ChS
import ../../laws/child.bend as Child
import ../base/child.bend as LChild
import ./base.bend as LA

def Child.child_quiet_poll_spends_time(s, f, tok, l, n, e):
  %LChild.pc.moved_self(tok) : {Ch.busy(_, Ch.Cfg{s, f}, Ch.W{tok, l, n}, tok, e) == ChS.ChildSpends(tok, l, e, f) : Ch.Next}
  LA.pc.spends(l, e, tok, f)
