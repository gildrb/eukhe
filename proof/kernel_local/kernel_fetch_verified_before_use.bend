# eukhe: the proof of LAW kernel_fetch_verified_before_use

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def pk.fetch_verified_before_use(f: KL.Found, s: KL.Setup) -> {KL.acts.verified(KL.plan(f, s), True{}) == True{} : Bool}:
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

def KernelLocal.kernel_fetch_verified_before_use(f, s):
  pk.fetch_verified_before_use(f, s)
