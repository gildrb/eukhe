# eukhe: the proof of LAW approvals_desk_entry_reads
# Each field reads back by the wire's round trips (LAAp.ae.rt).

import Base
import ../../laws/approvals/entry.bend as ApprovalsEntry
import ./base/entry.bend as LAAp

def ApprovalsEntry.approvals_desk_entry_reads(e, rest, h):
  LAAp.ae.rt(e, rest, h)
