# eukhe: the proof of LAW kernel_runs_means_a_run
#
# Induction on the list: the first start is the witness (nothing before
# it); an action that is no start goes before the witness of the rest; the
# empty list does not run.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def krm.G(xs: List<&2, KL.Act>) -> Type:
  &pre: List<&2, KL.Act> -> &post: List<&2, KL.Act> -> {xs == List.append(&2, KL.Act, pre, KL.Run{} <> post) : List<&2, KL.Act>}

# the witness of t, after x
def krm.cons(+x: KL.Act, -t: List<&2, KL.Act>, r: krm.G(t)) -> krm.G(x <> t):
  (pre, (post, e)) = r
  (x <> pre, (post, (%e : {x <> t == x <> _ : List<&2, KL.Act>}; {==})))

def KernelLocal.kernel_runs_means_a_run(xs, runs):
  match xs:
    case Nil{}:
      LKL.kl.absurd(krm.G(Nil{}), runs)
    case +x <> +t:
      match x:
        case KL.Run{}:
          (Nil{}, (t, {==}))
        case KL.Fetch{+g}:
          krm.cons(KL.Fetch{g}, t, KernelLocal.kernel_runs_means_a_run(t, runs))
        case KL.Offline{}:
          krm.cons(KL.Offline{}, t, KernelLocal.kernel_runs_means_a_run(t, runs))
        case KL.Check{}:
          krm.cons(KL.Check{}, t, KernelLocal.kernel_runs_means_a_run(t, runs))
