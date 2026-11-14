# eukhe: the proof of LAW server_peer_no_record
#
# PROOF: the uid compares equal to itself (spb.eq_refl); a record of 0 is
# none.

import Base
import ../../bend/server_peer.bend as Sp
import ../../laws/server_peer.bend as ServerPeer
import ./base.bend as LA

def ServerPeer.server_peer_no_record(own, pid):
  %LA.spb.eq_refl(own) : {Sp.served.uid(_, pid, 0n) == Sp.NoRecord{} : Sp.Served}
  {==}
