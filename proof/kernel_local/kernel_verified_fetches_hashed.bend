# eukhe: the proof of LAW kernel_verified_fetches_hashed
#
# Induction on the actions before the fetch: each passes a verified list
# on to its rest (a Bool.and that is True has both sides True); at the
# place itself a fetch's Bool.and(h, ..) is True, so h is, and an action
# that fetches nothing is hashed by definition.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def KernelLocal.kernel_verified_fetches_hashed(pre, x, post, ok):
  match pre:
    case Nil{}:
      match x:
        case KL.FetchUv{+h}:
          LKL.kl.and_l(h, KL.acts.verified(post), ok)
        case KL.FetchPython{+h}:
          LKL.kl.and_l(h, KL.acts.verified(post), ok)
        case KL.MakeEnv{}:
          {==}
        case KL.Run{}:
          {==}
    case y <> t:
      match y:
        case KL.FetchUv{+g}:
          KernelLocal.kernel_verified_fetches_hashed(t, x, post, LKL.kl.and_r(g, KL.acts.verified(List.append(&2, KL.Act, t, x <> post)), ok))
        case KL.FetchPython{+g}:
          KernelLocal.kernel_verified_fetches_hashed(t, x, post, LKL.kl.and_r(g, KL.acts.verified(List.append(&2, KL.Act, t, x <> post)), ok))
        case KL.MakeEnv{}:
          KernelLocal.kernel_verified_fetches_hashed(t, x, post, ok)
        case KL.Run{}:
          KernelLocal.kernel_verified_fetches_hashed(t, x, post, ok)
