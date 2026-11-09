# eukhe: the proof of LAW kernel_verified_checks_between
#
# Two inductions. Before the fetch: a verified list passes verified on to
# its rest, from any clean flag, and a fetch leaves the rest verified from
# "not clean". After the fetch, from "not clean": a start before any check
# is refused (Bool.and(False, ..)), so a check comes before the start.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def kvc.pre(a: List<&2, KL.Act>, +c: Bool, h: Bool, -z: List<&2, KL.Act>, ok: {KL.acts.verified(List.append(&2, KL.Act, a, KL.Fetch{h} <> z), c) == True{} : Bool}) -> {KL.acts.verified(z, False{}) == True{} : Bool}:
  match a:
    case Nil{}:
      LKL.kl.and_r(h, KL.acts.verified(z, False{}), ok)
    case x <> t:
      match x:
        case KL.Fetch{+g}:
          kvc.pre(t, False{}, h, z, LKL.kl.and_r(g, KL.acts.verified(List.append(&2, KL.Act, t, KL.Fetch{h} <> z), False{}), ok))
        case KL.Offline{}:
          kvc.pre(t, c, h, z, ok)
        case KL.Check{}:
          kvc.pre(t, True{}, h, z, ok)
        case KL.Run{}:
          kvc.pre(t, c, h, z, LKL.kl.and_r(c, KL.acts.verified(List.append(&2, KL.Act, t, KL.Fetch{h} <> z), c), ok))

def kvc.post(b: List<&2, KL.Act>, -c: List<&2, KL.Act>, ok: {KL.acts.verified(List.append(&2, KL.Act, b, KL.Run{} <> c), False{}) == True{} : Bool}) -> {KernelLocal.kl_has_check(b) == True{} : Bool}:
  match b:
    case Nil{}:
      LKL.kl.absurd({KernelLocal.kl_has_check(Nil{}) == True{} : Bool}, ok)
    case x <> t:
      match x:
        case KL.Fetch{+g}:
          kvc.post(t, c, LKL.kl.and_r(g, KL.acts.verified(List.append(&2, KL.Act, t, KL.Run{} <> c), False{}), ok))
        case KL.Offline{}:
          kvc.post(t, c, ok)
        case KL.Check{}:
          {==}
        case KL.Run{}:
          LKL.kl.absurd({KernelLocal.kl_has_check(KL.Run{} <> t) == True{} : Bool}, ok)

def KernelLocal.kernel_verified_checks_between(a, h, b, c, ok):
  kvc.post(b, c, kvc.pre(a, True{}, h, List.append(&2, KL.Act, b, KL.Run{} <> c), ok))
