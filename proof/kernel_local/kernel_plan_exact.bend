# eukhe: the proof of LAW kernel_plan_exact

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def KernelLocal.kernel_plan_exact(f, s):
  match f s:
    case KL.Current{} KL.Local{}:
      {==}
    case KL.Current{} KL.Install{}:
      {==}
    case KL.Skills{} KL.Local{}:
      {==}
    case KL.Skills{} KL.Install{}:
      {==}
    case KL.Stale{} KL.Local{}:
      {==}
    case KL.Stale{} KL.Install{}:
      {==}
