# eukhe: the proof of LAW path_policy_ffi_rejects_malformed

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/path_policy.bend as PathPolicy

def PathPolicy.path_policy_ffi_rejects_malformed(s, bad):
  %Equal.sym(Wr.Dec<FPp.Req>, FPp.get_req(s), Wr.Bad{}, bad) : {LawsBase.wire_opens_err(FPp.answer(_)) == True{} : Bool}
  {==}
