# eukhe: the proof of LAW package_source_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (pse.req_rt), so the entry answers the model's answer, spelled by
# encoders that are the spec spellers (pse.parsed, pse.gitans, pse.spec).

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/ffi_package_source.bend as FPs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/package_source/entry.bend as PackageSourceEntry
import ./base/entry.bend as LE

def psa.reply(q: FPs.Req) -> {FPs.answer(q) == PackageSourceEntry.ps_w_reply(q) : String}:
  match q:
    case FPs.QSource{+x}:
      LE.pse.parsed(Ps.source(x))
    case FPs.QGit{+x}:
      LE.pse.gitans(Ps.git(x))
    case FPs.QLocal{+x}:
      {==}
    case FPs.QNpm{+x}:
      LE.pse.spec(Ps.npm_spec(x))
    case FPs.QPart{+p}:
      {==}
    case FPs.QDefect{+d}:
      {==}
    case FPs.QError{+x, +f}:
      {==}

def PackageSourceEntry.package_source_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FPs.Req>, FPs.get_req(PackageSourceEntry.ps_w_req(q, "")), Wr.Got{q, ""}, LE.pse.req_rt(q, "", fit)) : {FPs.ffi.got(_) == PackageSourceEntry.ps_w_reply(q) : String}
  psa.reply(q)
