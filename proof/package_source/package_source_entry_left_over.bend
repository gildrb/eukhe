# eukhe: the proof of LAW package_source_entry_left_over
#
# PROOF: the spelled request reads back with the extra input left (pse.req_rt), which the entry refuses.

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/ffi_package_source.bend as FPs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/package_source/model.bend as PackageSource
import ../../laws/package_source/entry.bend as PackageSourceEntry
import ./base/entry.bend as LE

def PackageSourceEntry.package_source_entry_left_over(q, c, t, fit):
  %Equal.sym(Wr.Dec<FPs.Req>, FPs.get_req(PackageSourceEntry.ps_w_req(q, SCon{c, t})), Wr.Got{q, SCon{c, t}}, LE.pse.req_rt(q, SCon{c, t}, fit)) : {FPs.ffi.got(_) == Wr.err("package_source: malformed request") : String}
  {==}
