# eukhe: the proof of LAW bash_gated_each_step
#
# PROOF: closed: the lookup computes.

import Base
import ../../bend/runners.bend as Ru
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/runners.bend as Runners
import ../base/staging.bend as LStg

def Runners.bash_gated_each_step():
  {==}
