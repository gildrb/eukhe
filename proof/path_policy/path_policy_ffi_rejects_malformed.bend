# eukhe: the proof of LAW path_policy_ffi_rejects_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_path_policy.bend as FPp
import ../../LAWS.bend as Laws

def Laws.path_policy_ffi_rejects_malformed(s, bad):
  %Equal.sym(Wr.Dec<FPp.Req>, FPp.get_req(s), Wr.Bad{}, bad) : {Laws.wire_opens_err(FPp.answer(_)) == True{} : Bool}
  {==}
