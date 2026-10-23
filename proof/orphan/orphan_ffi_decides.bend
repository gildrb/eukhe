# eukhe: the proof of LAW orphan_ffi_decides

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/orphan.bend as Or
import ../../bend/wire.bend as Wr
import ../../laws/orphan.bend as Orphan

def Orphan.orphan_ffi_decides(s, m, a, k, h):
  %Equal.sym(Wr.Dec<FO.Req>, FO.get_req(s), Wr.Got{FO.Req{m, a, k}, ""}, h) : {FO.ffi.go(_) == FO.put_reply(FO.Reply{Or.exit_due.at(m, a, k), Or.orphan_exit(k)}, "") : String}
  {==}
