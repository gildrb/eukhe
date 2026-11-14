# eukhe: the proof of LAW server_peer_entry_refuses
#
# PROOF: the entry answers either a verdict, which opens with a Nat (never
# 'E': wire_nat_not_err), or the one error form; so an answer that opens
# with 'E' is that error form.

import Base
import ../../bend/server_peer.bend as Sp
import ../../bend/ffi_server_peer.bend as FSp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/server_peer.bend as ServerPeer
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

# a verdict never opens with 'E'
def spf.answer_ok(q: FSp.Req) -> {LawsBase.wire_opens_err(FSp.answer(q)) == False{} : Bool}:
  match q:
    case FSp.Req{p, o, i, c}:
      Wire.wire_nat_not_err(FSp.tag(Sp.served(p, o, i, c)), "")

def spf.refuse(d: Wr.Dec<FSp.Req>, bad: {LawsBase.wire_opens_err(FSp.ffi.got(d)) == True{} : Bool}) -> {FSp.ffi.got(d) == Wr.err("server_peer: malformed request") : String}:
  match d:
    case Wr.Got{q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FSp.answer(q) == Wr.err("server_peer: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FSp.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FSp.answer(q)), True{}, bad), spf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def ServerPeer.server_peer_entry_refuses(s, bad):
  spf.refuse(FSp.get_req(s), bad)
