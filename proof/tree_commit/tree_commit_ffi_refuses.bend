# eukhe: the proof of LAW tree_commit_ffi_refuses

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

# PROOF of LAW tree_commit_ffi_refuses: the entry answers either the error form or a reply, and a reply opens with its count, never 'E' (tce.reply_not_err).

def tcr.done(+cs: List<&2, Tc.Ch>, b: Bool, bad: {LawsBase.wire_opens_err(FTc.ffi.done(cs, b)) == True{} : Bool}) -> {FTc.ffi.done(cs, b) == Wr.err("tree_commit: malformed request") : String}:
  match b:
    case True{}:
      LATcEntry.tce.tf({FTc.answer(cs) == Wr.err("tree_commit: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FTc.answer(cs)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FTc.answer(cs)), True{}, bad), LATcEntry.tce.reply_not_err(Tc.order(cs))))
    case False{}:
      {==}

def tcr.got(d: Wr.Dec<List<&2, Tc.Ch>>, bad: {LawsBase.wire_opens_err(FTc.ffi.got(d)) == True{} : Bool}) -> {FTc.ffi.got(d) == Wr.err("tree_commit: malformed request") : String}:
  match d:
    case Wr.Got{+cs, +r}:
      tcr.done(cs, Wr.end(r), bad)
    case Wr.Bad{}:
      {==}

def TreeCommit.tree_commit_ffi_refuses(s, bad):
  tcr.got(FTc.get_req(s), bad)
