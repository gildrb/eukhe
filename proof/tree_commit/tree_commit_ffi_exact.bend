# eukhe: the proof of LAW tree_commit_ffi_exact

import Base
import ../../bend/tree_commit.bend as Tc
import ../../bend/ffi_tree_commit.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/tree_commit.bend as TreeCommit
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ./base.bend as LATreeCommit
import ./base/entry.bend as LATcEntry

# PROOF of LAW tree_commit_ffi_exact: the request decoder answers Got only for a spelled request whose count and keys fit (tce.req: wire_nat_exact and wire_nat_decoded_fits, change by change); the entry answers a value only when nothing is left after it.

def tcx.top(-s: String, d: Wr.Dec<List<&2, Tc.Ch>>, p: LATcEntry.tce.LS(s, d), ok: {LawsBase.wire_opens_err(FTc.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, List<&2, Tc.Ch>, r2 => {s == TreeCommit.spell_req(r2, "") : String} & {TreeCommit.req_fits(r2) == True{} : Bool}>:
  match d:
    case Wr.Got{+r, rest}:
      match rest:
        case SNil{}:
          (r, p)
        case SCon{x, y}:
          LATcEntry.tce.tf(Sigma<&1, &1, List<&2, Tc.Ch>, r2 => {s == TreeCommit.spell_req(r2, "") : String} & {TreeCommit.req_fits(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LATcEntry.tce.tf(Sigma<&1, &1, List<&2, Tc.Ch>, r2 => {s == TreeCommit.spell_req(r2, "") : String} & {TreeCommit.req_fits(r2) == True{} : Bool}>, ok)

def TreeCommit.tree_commit_ffi_exact(s, ok):
  tcx.top(s, FTc.get_req(s), LATcEntry.tce.req(s), ok)
