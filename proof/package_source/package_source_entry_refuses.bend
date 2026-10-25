# eukhe: the proof of LAW package_source_entry_refuses
#
# PROOF: every answer opens with a Nat or a Bool, never 'E' (pse.reply_ok); so an answer that opens with 'E' is the one error form.

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/ffi_package_source.bend as FPs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/package_source/model.bend as PackageSource
import ../../laws/package_source/entry.bend as PackageSourceEntry
import ./base/entry.bend as LE
import ../base/staging.bend as LStg

def psf.refuse(d: Wr.Dec<FPs.Req>, bad: {LawsBase.wire_opens_err(FPs.ffi.got(d)) == True{} : Bool}) -> {FPs.ffi.got(d) == Wr.err("package_source: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FPs.answer(q) == Wr.err("package_source: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FPs.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FPs.answer(q)), True{}, bad), LE.pse.reply_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def PackageSourceEntry.package_source_entry_refuses(s, bad):
  psf.refuse(FPs.get_req(s), bad)
