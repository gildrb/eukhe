# eukhe: the proof of LAW lease_entry_reads
# The entry's decoder answers what the laws' reader answers on every input
# (LA.le.read); a whole event steps the lease by the model and the reply
# is the laws' spelling of the model's grant and ended keys (LA.le.reply).

import Base
import ../../bend/lease.bend as Ls
import ../../bend/ffi_lease.bend as FLs
import ../../laws/lease.bend as Lease
import ./base.bend as LA

def Lease.lease_entry_reads(s, i, e, got):
  LA.le.reads(s, i, e, got)
