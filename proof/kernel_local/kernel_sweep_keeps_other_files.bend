# eukhe: the proof of LAW kernel_sweep_keeps_other_files
#
# Induction on the files and the index together: past the head, the
# index steps down on both lists; at the head, the file is another file
# (Some is injective), so its verdict computes to keep for either owner;
# no file: the premise is None == Some.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal
import ./base.bend as LKL

def kso.at(o: KL.Owner, -l: KL.Left, e: {KL.Left{KL.Foreign{}, o} == l : KL.Left}) -> {Some{KL.keep(l)} == Some{True{}} : Maybe<&2, Bool>}:
  match o:
    case KL.Alive{}:
      %e : {Some{KL.keep(_)} == Some{True{}} : Maybe<&2, Bool>}
      {==}
    case KL.Dead{}:
      %e : {Some{KL.keep(_)} == Some{True{}} : Maybe<&2, Bool>}
      {==}

def KernelLocal.kernel_sweep_keeps_other_files(ls, i, o, at):
  match ls i:
    case Nil{} _:
      LKL.kl.none_some(KL.Left, KL.Left{KL.Foreign{}, o}, {List.get(&2, Bool, KL.keeps(Nil{}), i) == Some{True{}} : Maybe<&2, Bool>}, at)
    case +l <> t 0n:
      kso.at(o, l, Equal.sym(KL.Left, l, KL.Left{KL.Foreign{}, o}, LKL.kl.some_inj(KL.Left, l, KL.Left{KL.Foreign{}, o}, at)))
    case l <> t 1n+p:
      KernelLocal.kernel_sweep_keeps_other_files(t, p, o, at)
