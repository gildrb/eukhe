# eukhe: the proof of LAW cow_entry_exact
# The entry reads every input as the laws' reader does and answers what
# the laws spell (LAC.cse.exact).

import Base
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LAC

def Sandbox.cow_entry_exact(s):
  LAC.cse.exact(s)
