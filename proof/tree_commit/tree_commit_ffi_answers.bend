# eukhe: the proof of LAW tree_commit_ffi_answers

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
import ./tree_commit_ffi_reads.bend as PTreeCommitFfiReads

# PROOF of LAW tree_commit_ffi_answers: the entry reads the request back whole with nothing left (tree_commit_ffi_reads) and answers the model's order with an encoder equal to the spec's (tce.reply).

def TreeCommit.tree_commit_ffi_answers(cs, h):
  %Equal.sym(Wr.Dec<List<&2, Tc.Ch>>, FTc.get_req(TreeCommit.spell_req(cs, "")), Wr.Got{cs, ""}, TreeCommit.tree_commit_ffi_reads(cs, "", h)) : {FTc.ffi.got(_) == TreeCommit.spell_reply(Tc.order(cs)) : String}
  LATcEntry.tce.reply(Tc.order(cs))
