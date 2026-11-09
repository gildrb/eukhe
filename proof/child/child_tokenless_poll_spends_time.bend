# eukhe: the proof of LAW child_tokenless_poll_spends_time
#
# PROOF: a poll with no token never moved, so it spends the elapsed ms
# off the clock (LA.pc.spends).

import Base
import ../../laws/child.bend as Child
import ./base.bend as LA

def Child.child_tokenless_poll_spends_time(s, f, tok, l, n, e):
  LA.pc.spends(l, e, tok, f)
