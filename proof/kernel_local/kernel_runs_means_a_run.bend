# eukhe: the proof of LAW kernel_runs_means_a_run
#
# Induction on the list: a start with nothing after it is the witness
# (nothing before it, so no start there); a start with actions after it
# does not end started; an action that is no start goes before the
# witness of the rest; the empty list does not end started.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def krm.G(xs: List<&2, KL.Act>) -> Type:
  &pre: List<&2, KL.Act> -> ({xs == List.append(&2, KL.Act, pre, [KL.Run{}]) : List<&2, KL.Act>} & {KernelLocal.kl_has_run(pre) == False{} : Bool})

# a list that starts with an action that is no start has a start only in
# its rest
def krm.has(x: KL.Act, -pre: List<&2, KL.Act>, nr: {KernelLocal.kl_is_run(x) == False{} : Bool}, n: {KernelLocal.kl_has_run(pre) == False{} : Bool}) -> {KernelLocal.kl_has_run(x <> pre) == False{} : Bool}:
  match x:
    case KL.FetchUv{h}:
      n
    case KL.FetchPython{h}:
      n
    case KL.MakeEnv{}:
      n
    case KL.Run{}:
      LKL.kl.absurd({KernelLocal.kl_has_run(KL.Run{} <> pre) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, nr))

# the witness of t, after x, an action that is no start
def krm.cons(+x: KL.Act, -t: List<&2, KL.Act>, nr: {KernelLocal.kl_is_run(x) == False{} : Bool}, r: krm.G(t)) -> krm.G(x <> t):
  (pre, (e, n)) = r
  (x <> pre, ((%e : {x <> t == x <> _ : List<&2, KL.Act>}; {==}), krm.has(x, pre, nr, n)))

def KernelLocal.kernel_runs_means_a_run(xs, ends):
  match xs:
    case Nil{}:
      LKL.kl.absurd(krm.G(Nil{}), ends)
    case +x <> +t:
      match x:
        case KL.Run{}:
          match t:
            case Nil{}:
              (Nil{}, ({==}, {==}))
            case y <> u:
              LKL.kl.absurd(krm.G(KL.Run{} <> y <> u), ends)
        case KL.FetchUv{+g}:
          krm.cons(KL.FetchUv{g}, t, {==}, KernelLocal.kernel_runs_means_a_run(t, ends))
        case KL.FetchPython{+g}:
          krm.cons(KL.FetchPython{g}, t, {==}, KernelLocal.kernel_runs_means_a_run(t, ends))
        case KL.MakeEnv{}:
          krm.cons(KL.MakeEnv{}, t, {==}, KernelLocal.kernel_runs_means_a_run(t, ends))
