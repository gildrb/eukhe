# eukhe: the proof of LAW server_peer_other_pid
#
# PROOF: the uid compares equal to itself (spb.eq_refl), the pid unequal
# to the record.

import Base
import ../../bend/server_peer.bend as Sp
import ../../laws/server_peer.bend as ServerPeer
import ./base.bend as LA

def ServerPeer.server_peer_other_pid(own, pid, q, ne):
  %LA.spb.eq_refl(own) : {Sp.served.uid(_, pid, 1n+q) == Sp.OtherPid{} : Sp.Served}
  %Equal.sym(Bool, Nat.is_eq(pid, 1n+q), False{}, ne) : {Sp.served.pid(_) == Sp.OtherPid{} : Sp.Served}
  {==}
