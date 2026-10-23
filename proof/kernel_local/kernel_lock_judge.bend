# eukhe: the proof of LAW kernel_lock_judge

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def kj.old(old: Bool) -> {KL.attempt(KL.lock.past(old)) == KernelLocal.judge_spec.old(old) : KL.End}:
  match old:
    case True{}:
      {==}
    case False{}:
      {==}

def KernelLocal.kernel_lock_judge(x):
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
          kj.old(Nat.is_lt(30000n, a))
