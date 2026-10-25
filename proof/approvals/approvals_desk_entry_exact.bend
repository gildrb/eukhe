# eukhe: the proof of LAW approvals_desk_entry_exact
# The entry's decoder is the laws' reader and its encoders the laws'
# spellers (LAAp.ae.exact).

import Base
import ../../laws/approvals/entry.bend as ApprovalsEntry
import ./base/entry.bend as LAAp

def ApprovalsEntry.approvals_desk_entry_exact(d, s):
  LAAp.ae.exact(d, s)
