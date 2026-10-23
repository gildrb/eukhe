# eukhe: the proof of LAW kernel_lock_sweep_keeps_live

import Base
import ../../bend/kernel_local.bend as KL
import ../../LAWS.bend as Laws

def pk.sweep_keeps_live(ls: List<&2, KL.Left>) -> {KL.lefts.live(KL.sweep(ls)) == KL.lefts.live(ls) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case KL.Left{k, o} <> rest:
      match k o:
        case KL.Cand{} KL.Alive{}:
          %pk.sweep_keeps_live(rest) : {1n+KL.lefts.live(KL.sweep(rest)) == 1n+_ : Nat}
          {==}
        case KL.Cand{} KL.Dead{}:
          pk.sweep_keeps_live(rest)
        case KL.Aside{} KL.Alive{}:
          %pk.sweep_keeps_live(rest) : {1n+KL.lefts.live(KL.sweep(rest)) == 1n+_ : Nat}
          {==}
        case KL.Aside{} KL.Dead{}:
          pk.sweep_keeps_live(rest)
        case KL.Foreign{} KL.Alive{}:
          %pk.sweep_keeps_live(rest) : {1n+KL.lefts.live(KL.sweep(rest)) == 1n+_ : Nat}
          {==}
        case KL.Foreign{} KL.Dead{}:
          %pk.sweep_keeps_live(rest) : {1n+KL.lefts.live(KL.sweep(rest)) == 1n+_ : Nat}
          {==}

def Laws.kernel_lock_sweep_keeps_live(ls):
  pk.sweep_keeps_live(ls)
