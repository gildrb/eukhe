# eukhe: the proof of LAW runners_ffi_exact
# The entry reads every input as the laws' reader does and answers what
# the laws spell (LARn.ru.exact).

import Base
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/runners.bend as Runners
import ./base/entry.bend as LARn

def Runners.runners_ffi_exact(s):
  LARn.rn.exact(s)
