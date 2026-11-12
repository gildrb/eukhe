# eukhe: the proof of LAW kernel_sweep_keeps_live_owner
#
# Induction on the files and the index together: past the head, the
# index steps down on both lists; at the head, the file is the live
# owner's (Some is injective), so its verdict computes to keep for every
# kind; no file: the premise is None == Some.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def ksl.at(k: KL.FileKind, -l: KL.Left, e: {KL.Left{k, KL.Alive{}} == l : KL.Left}) -> {Some{KL.keep(l)} == Some{True{}} : Maybe<&2, Bool>}:
  match k:
    case KL.Cand{}:
      %e : {Some{KL.keep(_)} == Some{True{}} : Maybe<&2, Bool>}
      {==}
    case KL.Aside{}:
      %e : {Some{KL.keep(_)} == Some{True{}} : Maybe<&2, Bool>}
      {==}
    case KL.Foreign{}:
      %e : {Some{KL.keep(_)} == Some{True{}} : Maybe<&2, Bool>}
      {==}

def KernelLocal.kernel_sweep_keeps_live_owner(ls, i, k, at):
  match ls i:
    case Nil{} _:
      LKL.kl.none_some(KL.Left, KL.Left{k, KL.Alive{}}, {List.get(&2, Bool, KL.keeps(Nil{}), i) == Some{True{}} : Maybe<&2, Bool>}, at)
    case +l <> t 0n:
      ksl.at(k, l, Equal.sym(KL.Left, l, KL.Left{k, KL.Alive{}}, LKL.kl.some_inj(KL.Left, l, KL.Left{k, KL.Alive{}}, at)))
    case l <> t 1n+p:
      KernelLocal.kernel_sweep_keeps_live_owner(t, p, k, at)
