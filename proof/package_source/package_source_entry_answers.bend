# eukhe: the proof of LAW package_source_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (pse.req_rt), so the entry answers the model's answer, the spec's (the model laws), spelled by encoders that are the spec spellers (pse.parsed, pse.gitans, pse.spec).

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/ffi_package_source.bend as FPs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/package_source/model.bend as PackageSource
import ../../laws/package_source/entry.bend as PackageSourceEntry
import ./base/entry.bend as LE
import ./package_source_source_spec.bend as PPackageSourceSourceSpec
import ./package_source_git_spec.bend as PPackageSourceGitSpec
import ./package_source_local_spec.bend as PPackageSourceLocalSpec
import ./package_source_npm_spec_spec.bend as PPackageSourceNpmSpecSpec
import ./package_source_part_text_spec.bend as PPackageSourcePartTextSpec
import ./package_source_defect_text_spec.bend as PPackageSourceDefectTextSpec
import ./package_source_error_text_spec.bend as PPackageSourceErrorTextSpec

def psa.reply(q: FPs.Req) -> {FPs.answer(q) == PackageSourceEntry.ps_w_reply(q) : String}:
  match q:
    case FPs.QSource{+x}:
      %PackageSource.package_source_source_spec(x) : {FPs.put_parsed(Ps.source(x)) == PackageSourceEntry.ps_w_parsed(_) : String}
      LE.pse.parsed(Ps.source(x))
    case FPs.QGit{+x}:
      %PackageSource.package_source_git_spec(x) : {FPs.put_gitans(Ps.git(x)) == PackageSourceEntry.ps_w_gitans(_) : String}
      LE.pse.gitans(Ps.git(x))
    case FPs.QLocal{+x}:
      %PackageSource.package_source_local_spec(x) : {Wr.put_bool(Ps.local(x), "") == Wr.put_bool(_, "") : String}
      {==}
    case FPs.QNpm{+x}:
      %PackageSource.package_source_npm_spec_spec(x) : {FPs.put_spec(Ps.npm_spec(x)) == PackageSourceEntry.ps_w_spec(_) : String}
      LE.pse.spec(Ps.npm_spec(x))
    case FPs.QPart{+p}:
      %PackageSource.package_source_part_text_spec(p) : {Wr.put_str(Ps.part_text(p), "") == Wr.put_str(_, "") : String}
      {==}
    case FPs.QDefect{+d}:
      %PackageSource.package_source_defect_text_spec(d) : {Wr.put_str(Ps.defect_text(d), "") == Wr.put_str(_, "") : String}
      {==}
    case FPs.QError{+x, +f}:
      %PackageSource.package_source_error_text_spec(x, f) : {Wr.put_str(Ps.error_text(x, f), "") == Wr.put_str(_, "") : String}
      {==}

def PackageSourceEntry.package_source_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FPs.Req>, FPs.get_req(PackageSourceEntry.ps_w_req(q, "")), Wr.Got{q, ""}, LE.pse.req_rt(q, "", fit)) : {FPs.ffi.got(_) == PackageSourceEntry.ps_w_reply(q) : String}
  psa.reply(q)
