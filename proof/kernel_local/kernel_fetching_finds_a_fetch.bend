# eukhe: the proof of LAW kernel_fetching_finds_a_fetch
#
# Induction on the actions before the fetch: each passes the test on to
# the rest, and the fetch answers True.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def KernelLocal.kernel_fetching_finds_a_fetch(pre, h, post):
  match pre:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case KL.Fetch{g}:
          {==}
        case KL.Offline{}:
          KernelLocal.kernel_fetching_finds_a_fetch(t, h, post)
        case KL.Check{}:
          KernelLocal.kernel_fetching_finds_a_fetch(t, h, post)
        case KL.Run{}:
          KernelLocal.kernel_fetching_finds_a_fetch(t, h, post)
