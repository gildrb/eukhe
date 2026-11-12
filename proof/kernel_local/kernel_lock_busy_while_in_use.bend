# eukhe: the proof of LAW kernel_lock_busy_while_in_use
#
# A live owner and an unknown age compute; a young age: the premise
# rewrites the age test to False.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def KernelLocal.kernel_lock_busy_while_in_use(a, young):
  ({==}, ({==}, (%Equal.sym(Bool, Nat.is_lt(30000n, a), False{}, young) : {KL.attempt(KL.lock.past(_)) == KL.Busy{} : KL.End}; {==})))
