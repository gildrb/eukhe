# eukhe: the proof of LAW server_peer_recorded_own_served
#
# PROOF: the uid compares equal to itself, then the pid to itself
# (spb.eq_refl).

import Base
import ../../bend/server_peer.bend as Sp
import ../../laws/server_peer.bend as ServerPeer
import ./base.bend as LA

def ServerPeer.server_peer_recorded_own_served(own, q):
  %LA.spb.eq_refl(own) : {Sp.served.uid(_, 1n+q, 1n+q) == Sp.Served{} : Sp.Served}
  %LA.spb.eq_refl(1n+q) : {Sp.served.pid(_) == Sp.Served{} : Sp.Served}
  {==}
