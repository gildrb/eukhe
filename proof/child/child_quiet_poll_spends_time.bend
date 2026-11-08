# eukhe: the proof of LAW child_quiet_poll_spends_time
#
# PROOF: the held token is no news (moved_self), so the poll spends the
# elapsed ms off the clock (LA.pc.spends).

import Base
import ../../bend/child.bend as Ch
import ../../laws/child.bend as Child
import ../base/child.bend as LChild
import ./base.bend as LA

def Child.child_quiet_poll_spends_time(cfg, w, e):
  match w:
    case Ch.W{+tok, +l, +n}:
      %LChild.pc.moved_self(tok) : {Ch.busy(_, cfg, Ch.W{tok, l, n}, tok, e) == Child.ChildSpends(tok, l, e, Ch.Cfg.fails(cfg)) : Ch.Next}
      LA.pc.spends(l, e, tok, Ch.Cfg.fails(cfg))
