# eukhe: the proof of LAW kernel_lock_frees_stale
#
# A dead owner and a vanished lock compute; an old age: the premise
# rewrites the age test to True.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def KernelLocal.kernel_lock_frees_stale(a, old):
  ({==}, ({==}, (%Equal.sym(Bool, Nat.is_lt(30000n, a), True{}, old) : {KL.attempt(KL.lock.past(_)) == KL.Freed{} : KL.End}; {==})))
