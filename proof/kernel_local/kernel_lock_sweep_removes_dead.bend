# eukhe: the proof of LAW kernel_lock_sweep_removes_dead

import Base
import ../../bend/kernel_local.bend as KL
import ../../LAWS.bend as Laws

def pk.sweep_removes_dead(ls: List<&2, KL.Left>) -> {KL.lefts.dead(KL.sweep(ls)) == 0n : Nat}:
  match ls:
    case Nil{}:
      {==}
    case KL.Left{k, o} <> rest:
      match k o:
        case KL.Cand{} KL.Alive{}:
          pk.sweep_removes_dead(rest)
        case KL.Cand{} KL.Dead{}:
          pk.sweep_removes_dead(rest)
        case KL.Aside{} KL.Alive{}:
          pk.sweep_removes_dead(rest)
        case KL.Aside{} KL.Dead{}:
          pk.sweep_removes_dead(rest)
        case KL.Foreign{} KL.Alive{}:
          pk.sweep_removes_dead(rest)
        case KL.Foreign{} KL.Dead{}:
          pk.sweep_removes_dead(rest)

def Laws.kernel_lock_sweep_removes_dead(ls):
  pk.sweep_removes_dead(ls)
