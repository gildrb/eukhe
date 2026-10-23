# eukhe: the proof of LAW kernel_start_exact

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def KernelLocal.kernel_start_exact(f, ok):
  match f ok:
    case KL.Current{} True{}:
      {==}
    case KL.Current{} False{}:
      {==}
    case KL.Skills{} True{}:
      {==}
    case KL.Skills{} False{}:
      {==}
    case KL.Stale{} True{}:
      {==}
    case KL.Stale{} False{}:
      {==}
