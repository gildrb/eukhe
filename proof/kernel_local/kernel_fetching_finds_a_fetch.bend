# eukhe: the proof of LAW kernel_fetching_finds_a_fetch
#
# Induction on the actions before the fetch: each passes the test on to
# the rest, and a fetch (of the uv or of the CPython) answers True; an
# action that is no fetch at that place contradicts the premise.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def KernelLocal.kernel_fetching_finds_a_fetch(pre, x, post, fetch):
  match pre:
    case Nil{}:
      match x:
        case KL.FetchUv{h}:
          {==}
        case KL.FetchPython{h}:
          {==}
        case KL.MakeEnv{}:
          LKL.kl.absurd({KL.acts.fetching(KL.MakeEnv{} <> post) == True{} : Bool}, fetch)
        case KL.Run{}:
          LKL.kl.absurd({KL.acts.fetching(KL.Run{} <> post) == True{} : Bool}, fetch)
    case y <> t:
      match y:
        case KL.FetchUv{g}:
          {==}
        case KL.FetchPython{g}:
          {==}
        case KL.MakeEnv{}:
          KernelLocal.kernel_fetching_finds_a_fetch(t, x, post, fetch)
        case KL.Run{}:
          KernelLocal.kernel_fetching_finds_a_fetch(t, x, post, fetch)
