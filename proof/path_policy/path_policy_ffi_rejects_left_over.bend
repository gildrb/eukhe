# eukhe: the proof of LAW path_policy_ffi_rejects_left_over

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/path_policy.bend as PathPolicy

def PathPolicy.path_policy_ffi_rejects_left_over(s, q, r, got, more):
  %Equal.sym(Wr.Dec<FPp.Req>, FPp.get_req(s), Wr.Got{q, r}, got) : {LawsBase.wire_opens_err(FPp.answer(_)) == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(r), False{}, more) : {LawsBase.wire_opens_err(FPp.reply(_, q)) == True{} : Bool}
  {==}
