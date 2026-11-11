# eukhe: the proof of LAW budget_recover_charges_in_full
#
# PROOF: a held id settled at w, what it holds: spent grows by w; free
# becomes (free + w) - w = free; the overrun grows by w - (free + w) = 0.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ./base/settle.bend as BS

def Budget.budget_recover_charges_in_full(id, act, a, d, open, full):
  match a:
    case B.Acct{f, s, l, o, hs, u}:
      BS.bs.recover(id, act, f, s, l, o, hs, u, d, open, full)
