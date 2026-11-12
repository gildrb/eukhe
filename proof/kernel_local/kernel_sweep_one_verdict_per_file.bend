# eukhe: the proof of LAW kernel_sweep_one_verdict_per_file
#
# Induction on the files: one verdict per file.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def KernelLocal.kernel_sweep_one_verdict_per_file(ls):
  match ls:
    case Nil{}:
      {==}
    case l <> t:
      %KernelLocal.kernel_sweep_one_verdict_per_file(t) : {1n+List.length(&2, Bool, KL.keeps(t)) == 1n+_ : Nat}
      {==}
