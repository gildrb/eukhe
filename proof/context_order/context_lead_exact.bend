# eukhe: the proof of LAW context_lead_exact

import Base
import ../../bend/context_order.bend as Co
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo

# PROOF of LAW context_lead_exact: from index i the code answers the first message after the leading users when it is a system message past index 0 (co.lead); at index 0 that is the spec's (co.L.at).

def ContextOrder.context_lead_exact(rs):
  %LACo.co.L.at(ContextOrder.users(rs), rs) : {Co.lead(rs) == _ : Maybe<&2, Nat>}
  %LACo.co.add_z(ContextOrder.users(rs)) : {Co.lead(rs) == LACo.co.L(_, ContextOrder.system_at(ContextOrder.users(rs), rs)) : Maybe<&2, Nat>}
  LACo.co.lead(rs, 0n)
