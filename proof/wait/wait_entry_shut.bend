# eukhe: the proof of LAW wait_entry_shut
import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

def WaitLaws.wait_entry_shut(i):
  {==}
