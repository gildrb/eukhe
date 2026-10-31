# eukhe: the proof of LAW auth_read_reads
# The entry reads every input as the laws' reader does (LAR.ar.go);
# a whole request gets the verdict on it (LAR.ar.reply).

import Base
import ../../laws/auth_read.bend as AuthRead
import ./base.bend as LAR

def AuthRead.auth_read_reads(s, q, got):
  LAR.ar.ffi_reads(s, q, got)
