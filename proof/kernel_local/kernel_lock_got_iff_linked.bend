# eukhe: the proof of LAW kernel_lock_got_iff_linked
#
# A case split on what the attempt saw; an aged lock that names no owner
# is busy or freed, never got, whatever the age test answers.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def kgl.past(b: Bool) -> {KernelLocal.kl_got(KL.attempt(KL.lock.past(b))) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def KernelLocal.kernel_lock_got_iff_linked(x):
  match x:
    case KL.Linked{}:
      {==}
    case KL.Vanished{}:
      {==}
    case KL.Owner{alive}:
      match alive:
        case True{}:
          {==}
        case False{}:
          {==}
    case KL.NoOwner{age}:
      match age:
        case None{}:
          {==}
        case Some{a}:
          kgl.past(Nat.is_lt(30000n, a))
