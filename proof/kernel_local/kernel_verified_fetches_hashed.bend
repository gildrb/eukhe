# eukhe: the proof of LAW kernel_verified_fetches_hashed
#
# Induction on the actions before the fetch, from any clean flag: each
# passes a verified list on to its rest (a Bool.and that is True has both
# sides True); at the fetch, Bool.and(h, ..) is True, so h is.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def kvh.go(pre: List<&2, KL.Act>, +c: Bool, +h: Bool, -post: List<&2, KL.Act>, ok: {KL.acts.verified(List.append(&2, KL.Act, pre, KL.Fetch{h} <> post), c) == True{} : Bool}) -> {h == True{} : Bool}:
  match pre:
    case Nil{}:
      LKL.kl.and_l(h, KL.acts.verified(post, False{}), ok)
    case x <> t:
      match x:
        case KL.Fetch{+g}:
          kvh.go(t, False{}, h, post, LKL.kl.and_r(g, KL.acts.verified(List.append(&2, KL.Act, t, KL.Fetch{h} <> post), False{}), ok))
        case KL.Offline{}:
          kvh.go(t, c, h, post, ok)
        case KL.Check{}:
          kvh.go(t, True{}, h, post, ok)
        case KL.Run{}:
          kvh.go(t, c, h, post, LKL.kl.and_r(c, KL.acts.verified(List.append(&2, KL.Act, t, KL.Fetch{h} <> post), c), ok))

def KernelLocal.kernel_verified_fetches_hashed(pre, h, post, ok):
  kvh.go(pre, True{}, h, post, ok)
