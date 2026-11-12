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
  &pre: List<&2, KL.Act> -> &x: KL.Act -> &post: List<&2, KL.Act> -> ({xs == List.append(&2, KL.Act, pre, x <> post) : List<&2, KL.Act>} & {KernelLocal.kl_is_fetch(x) == True{} : Bool})

# the witness of t, after y
def kfm.cons(+y: KL.Act, -t: List<&2, KL.Act>, r: kfm.G(t)) -> kfm.G(y <> t):
  (pre, (x, (post, (e, f)))) = r
  (y <> pre, (x, (post, ((%e : {y <> t == y <> _ : List<&2, KL.Act>}; {==}), f))))

def KernelLocal.kernel_fetching_means_a_fetch(xs, fetches):
  match xs:
    case Nil{}:
      LKL.kl.absurd(kfm.G(Nil{}), fetches)
    case +x <> +t:
      match x:
        case KL.FetchUv{+g}:
          (Nil{}, (KL.FetchUv{g}, (t, ({==}, {==}))))
        case KL.FetchPython{+g}:
          (Nil{}, (KL.FetchPython{g}, (t, ({==}, {==}))))
        case KL.MakeEnv{}:
          kfm.cons(KL.MakeEnv{}, t, KernelLocal.kernel_fetching_means_a_fetch(t, fetches))
        case KL.Run{}:
          kfm.cons(KL.Run{}, t, KernelLocal.kernel_fetching_means_a_fetch(t, fetches))
