# eukhe: the proof of LAW verify_entry_example
#
# PROOF: closed: both sides compute.

import Base
import ../../bend/verify.bend as V
import ../../bend/ffi_verify.bend as FV
import ../../bend/wire.bend as Wr
import ../../spec/verified/verify_wire.bend as SW
import ../../laws/verify.bend as Verify

def Verify.verify_entry_example():
  {==}
