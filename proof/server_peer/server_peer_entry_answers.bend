# eukhe: the proof of LAW server_peer_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (server_peer_entry_reads), so the entry answers the model's verdict with
# its tag, which is Rust's (spa.tag: case by case).

import Base
import ../../bend/server_peer.bend as Sp
import ../../bend/ffi_server_peer.bend as FSp
import ../../bend/wire.bend as Wr
import ../../laws/server_peer.bend as ServerPeer
import ./server_peer_entry_reads.bend as PServerPeerEntryReads

def spa.tag(v: Sp.Served) -> {FSp.tag(v) == ServerPeer.sp_tag(v) : Nat}:
  match v:
    case Sp.Served{}:
      {==}
    case Sp.OtherUid{}:
      {==}
    case Sp.NoRecord{}:
      {==}
    case Sp.OtherPid{}:
      {==}

# the answer to a request read whole is its verdict under Rust's tag
def spa.answer(q: FSp.Req) -> {FSp.answer(q) == Wr.put_nat(ServerPeer.sp_tag(ServerPeer.sp_verdict(q)), "") : String}:
  match q:
    case FSp.Req{p, o, i, c}:
      %spa.tag(Sp.served(p, o, i, c)) : {Wr.put_nat(FSp.tag(Sp.served(p, o, i, c)), "") == Wr.put_nat(_, "") : String}
      {==}

def ServerPeer.server_peer_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FSp.Req>, FSp.get_req(ServerPeer.sp_spell(q, "")), Wr.Got{q, ""}, ServerPeer.server_peer_entry_reads(q, "", h)) : {FSp.ffi.got(_) == Wr.put_nat(ServerPeer.sp_tag(ServerPeer.sp_verdict(q)), "") : String}
  spa.answer(q)
