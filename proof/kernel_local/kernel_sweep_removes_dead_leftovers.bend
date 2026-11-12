# eukhe: the proof of LAW kernel_sweep_removes_dead_leftovers
#
# Induction on the files and the index together: past the head, the
# index steps down on both lists; at the head, the file is the dead
# owner's (Some is injective) and its kind an attempt's, so its verdict
# computes to remove; no file: the premise is None == Some.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def ksd.at(k: KL.FileKind, -l: KL.Left, e: {KL.Left{k, KL.Dead{}} == l : KL.Left}, mine: {KernelLocal.kl_attempt_file(k) == True{} : Bool}) -> {Some{KL.keep(l)} == Some{False{}} : Maybe<&2, Bool>}:
  match k:
    case KL.Cand{}:
      %e : {Some{KL.keep(_)} == Some{False{}} : Maybe<&2, Bool>}
      {==}
    case KL.Aside{}:
      %e : {Some{KL.keep(_)} == Some{False{}} : Maybe<&2, Bool>}
      {==}
    case KL.Foreign{}:
      LKL.kl.absurd({Some{KL.keep(l)} == Some{False{}} : Maybe<&2, Bool>}, mine)

def KernelLocal.kernel_sweep_removes_dead_leftovers(ls, i, k, at, mine):
  match ls i:
    case Nil{} _:
      LKL.kl.none_some(KL.Left, KL.Left{k, KL.Dead{}}, {List.get(&2, Bool, KL.keeps(Nil{}), i) == Some{False{}} : Maybe<&2, Bool>}, at)
    case +l <> t 0n:
      ksd.at(k, l, Equal.sym(KL.Left, l, KL.Left{k, KL.Dead{}}, LKL.kl.some_inj(KL.Left, l, KL.Left{k, KL.Dead{}}, at)), mine)
    case l <> t 1n+p:
      KernelLocal.kernel_sweep_removes_dead_leftovers(t, p, k, at, mine)
