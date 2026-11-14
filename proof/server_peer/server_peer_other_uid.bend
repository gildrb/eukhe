# eukhe: the proof of LAW server_peer_other_uid
#
# PROOF: the uids compare unequal, and the uid decides first.

import Base
import ../../bend/server_peer.bend as Sp
import ../../laws/server_peer.bend as ServerPeer

def ServerPeer.server_peer_other_uid(p, own, pid, rec, ne):
  %Equal.sym(Bool, Nat.is_eq(p, own), False{}, ne) : {Sp.served.uid(_, pid, rec) == Sp.OtherUid{} : Sp.Served}
  {==}
