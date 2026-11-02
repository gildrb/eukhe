# eukhe: the proof of LAW cow_ffi_exact
# The entry reads every input as the laws' reader does and answers what
# the laws spell (LACow.cw.exact).

import Base
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LACow

def Sandbox.cow_ffi_exact(s):
  LACow.cw.exact(s)
