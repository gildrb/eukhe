# eukhe: the proof of LAW rebase_entry_reads
#
# PROOF: each list decoder answers Got only for the spelling of what it
# read, within the wire (wire_list_exact, ge.nats_fit); a value is answered
# only for a request read whole whose flat edits read back, and flat edits
# that read back were spelled from them (fe.unflat_exact; fx.*).

import Base
import ../../bend/rebase.bend as R
import ../../bend/ffi_rebase.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/rebase.bend as Rebase
import ./base/entry.bend as LE


def Rebase.rebase_entry_reads(s, ok):
  LE.fx.base(s, Wr.get_list(~Nat, ~Wr.get_nat, s), {==}, ok)
