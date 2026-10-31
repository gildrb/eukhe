# eukhe: the proof of LAW rebase_entry_refuses
#
# PROOF: every outcome is spelled from a Nat, never 'E' (fe.out_ok); so an answer that opens with 'E' is the one error form (fe.refuse).

import Base
import ../../bend/rebase.bend as R
import ../../bend/ffi_rebase.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/rebase.bend as Rebase
import ./base/entry.bend as LE


def Rebase.rebase_entry_refuses(s, bad):
  LE.fe.refuse(FR.get_req(s), bad)
