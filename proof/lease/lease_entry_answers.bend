# eukhe: the proof of LAW lease_entry_answers
# The laws' reader reads the spelled event back (the wire's round trip,
# LA.le.rt); the entry reads every input as that reader does and steps a
# read event as the model, with the laws' reply (LA.le.reads).

import Base
import ../../bend/lease.bend as Ls
import ../../bend/ffi_lease.bend as FLs
import ../../laws/lease.bend as Lease
import ./base.bend as LA

def Lease.lease_entry_answers(s, e, fits):
  LA.le.answers(s, e, fits)
