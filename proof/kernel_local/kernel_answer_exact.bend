# eukhe: the proof of LAW kernel_answer_exact

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def KernelLocal.kernel_answer_exact(t, k):
  match t k:
    case KL.Python{} KL.Up{}:
      {==}
    case KL.Python{} KL.Missing{}:
      {==}
    case KL.Other{n} KL.Up{}:
      {==}
    case KL.Other{n} KL.Missing{}:
      {==}
