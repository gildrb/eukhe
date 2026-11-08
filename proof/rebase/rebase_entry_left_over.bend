# eukhe: the proof of LAW rebase_entry_left_over
#
# PROOF: the spelled request reads back with the extra input left (fe.req_rt), which the entry refuses.

import Base
import ../../bend/rebase.bend as R
import ../../bend/ffi_rebase.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/rebase.bend as Rebase
import ./base/entry.bend as LE


def Rebase.rebase_entry_left_over(b, h, es, c, t, fit):
  %Equal.sym(Wr.Dec<FR.Req>, FR.get_req(Rebase.rb_w_req(b, h, es, SCon{c, t})), Wr.Got{FR.Req{b, h, Rebase.rb_flat(es)}, SCon{c, t}}, LE.fe.req_rt(b, h, es, SCon{c, t}, fit)) : {FR.ffi.got(_) == Wr.err("rebase: malformed request") : String}
  {==}
