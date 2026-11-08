# eukhe: the proof of LAW wait_any_entry_premises_witness
#
# PROOF: closed computation.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../spec/durable/wait_any_wire.bend as SpW

def WaitAny.wait_any_entry_premises_witness():
  {==}
