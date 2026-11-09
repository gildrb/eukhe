# eukhe: the proof of LAW kernel_fetching_means_a_fetch
#
# Induction on the list: the first fetch is the witness (nothing before
# it); an action that is no fetch goes before the witness of the rest; the
# empty list does not fetch.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def kfm.G(xs: List<&2, KL.Act>) -> Type:
  &pre: List<&2, KL.Act> -> &h: Bool -> &post: List<&2, KL.Act> -> {xs == List.append(&2, KL.Act, pre, KL.Fetch{h} <> post) : List<&2, KL.Act>}

# the witness of t, after x
def kfm.cons(+x: KL.Act, -t: List<&2, KL.Act>, r: kfm.G(t)) -> kfm.G(x <> t):
  (pre, (h, (post, e))) = r
  (x <> pre, (h, (post, (%e : {x <> t == x <> _ : List<&2, KL.Act>}; {==}))))

def KernelLocal.kernel_fetching_means_a_fetch(xs, fetches):
  match xs:
    case Nil{}:
      LKL.kl.absurd(kfm.G(Nil{}), fetches)
    case +x <> +t:
      match x:
        case KL.Fetch{+g}:
          (Nil{}, (g, (t, {==})))
        case KL.Offline{}:
          kfm.cons(KL.Offline{}, t, KernelLocal.kernel_fetching_means_a_fetch(t, fetches))
        case KL.Check{}:
          kfm.cons(KL.Check{}, t, KernelLocal.kernel_fetching_means_a_fetch(t, fetches))
        case KL.Run{}:
          kfm.cons(KL.Run{}, t, KernelLocal.kernel_fetching_means_a_fetch(t, fetches))
