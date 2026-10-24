# eukhe: the proof of LAW frames_ffi_exact
# The entry reads every input as the laws' reader does and answers what
# the laws spell (LAFr.fr.exact).

import Base
import ../../laws/sandbox.bend as Sandbox
import ./base/frames.bend as LAFr

def Sandbox.frames_ffi_exact(s):
  LAFr.fr.exact(s)
