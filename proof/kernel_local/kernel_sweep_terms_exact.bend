# eukhe: the proof of LAW kernel_sweep_terms_exact
# Each term by induction on the files, one case per kind and owner.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def kt.sweep(ls: List<&2, KL.Left>) -> {KL.sweep(ls) == KernelLocal.sweep_spec(ls) : List<&2, KL.Left>}:
  match ls:
    case Nil{}:
      {==}
    case l <> rest:
      match l:
        case KL.Left{k, o}:
          match k o:
            case KL.Cand{} KL.Alive{}:
              %kt.sweep(rest) : {KL.keep.cons(KL.keep(KL.Left{KL.Cand{}, KL.Alive{}}), KL.Left{KL.Cand{}, KL.Alive{}}, KL.sweep(rest)) == KernelLocal.sweep_spec.cons(KernelLocal.keep_spec(KL.Left{KL.Cand{}, KL.Alive{}}), KL.Left{KL.Cand{}, KL.Alive{}}, _) : List<&2, KL.Left>}
              {==}
            case KL.Cand{} KL.Dead{}:
              %kt.sweep(rest) : {KL.keep.cons(KL.keep(KL.Left{KL.Cand{}, KL.Dead{}}), KL.Left{KL.Cand{}, KL.Dead{}}, KL.sweep(rest)) == KernelLocal.sweep_spec.cons(KernelLocal.keep_spec(KL.Left{KL.Cand{}, KL.Dead{}}), KL.Left{KL.Cand{}, KL.Dead{}}, _) : List<&2, KL.Left>}
              {==}
            case KL.Aside{} KL.Alive{}:
              %kt.sweep(rest) : {KL.keep.cons(KL.keep(KL.Left{KL.Aside{}, KL.Alive{}}), KL.Left{KL.Aside{}, KL.Alive{}}, KL.sweep(rest)) == KernelLocal.sweep_spec.cons(KernelLocal.keep_spec(KL.Left{KL.Aside{}, KL.Alive{}}), KL.Left{KL.Aside{}, KL.Alive{}}, _) : List<&2, KL.Left>}
              {==}
            case KL.Aside{} KL.Dead{}:
              %kt.sweep(rest) : {KL.keep.cons(KL.keep(KL.Left{KL.Aside{}, KL.Dead{}}), KL.Left{KL.Aside{}, KL.Dead{}}, KL.sweep(rest)) == KernelLocal.sweep_spec.cons(KernelLocal.keep_spec(KL.Left{KL.Aside{}, KL.Dead{}}), KL.Left{KL.Aside{}, KL.Dead{}}, _) : List<&2, KL.Left>}
              {==}
            case KL.Foreign{} KL.Alive{}:
              %kt.sweep(rest) : {KL.keep.cons(KL.keep(KL.Left{KL.Foreign{}, KL.Alive{}}), KL.Left{KL.Foreign{}, KL.Alive{}}, KL.sweep(rest)) == KernelLocal.sweep_spec.cons(KernelLocal.keep_spec(KL.Left{KL.Foreign{}, KL.Alive{}}), KL.Left{KL.Foreign{}, KL.Alive{}}, _) : List<&2, KL.Left>}
              {==}
            case KL.Foreign{} KL.Dead{}:
              %kt.sweep(rest) : {KL.keep.cons(KL.keep(KL.Left{KL.Foreign{}, KL.Dead{}}), KL.Left{KL.Foreign{}, KL.Dead{}}, KL.sweep(rest)) == KernelLocal.sweep_spec.cons(KernelLocal.keep_spec(KL.Left{KL.Foreign{}, KL.Dead{}}), KL.Left{KL.Foreign{}, KL.Dead{}}, _) : List<&2, KL.Left>}
              {==}

def kt.dead(ls: List<&2, KL.Left>) -> {KL.lefts.dead(ls) == KernelLocal.dead_spec(ls) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case l <> rest:
      match l:
        case KL.Left{k, o}:
          match k o:
            case KL.Cand{} KL.Alive{}:
              %kt.dead(rest) : {Nat.add(KL.dead(KL.Left{KL.Cand{}, KL.Alive{}}), KL.lefts.dead(rest)) == Nat.add(KernelLocal.dead_one(KL.Left{KL.Cand{}, KL.Alive{}}), _) : Nat}
              {==}
            case KL.Cand{} KL.Dead{}:
              %kt.dead(rest) : {Nat.add(KL.dead(KL.Left{KL.Cand{}, KL.Dead{}}), KL.lefts.dead(rest)) == Nat.add(KernelLocal.dead_one(KL.Left{KL.Cand{}, KL.Dead{}}), _) : Nat}
              {==}
            case KL.Aside{} KL.Alive{}:
              %kt.dead(rest) : {Nat.add(KL.dead(KL.Left{KL.Aside{}, KL.Alive{}}), KL.lefts.dead(rest)) == Nat.add(KernelLocal.dead_one(KL.Left{KL.Aside{}, KL.Alive{}}), _) : Nat}
              {==}
            case KL.Aside{} KL.Dead{}:
              %kt.dead(rest) : {Nat.add(KL.dead(KL.Left{KL.Aside{}, KL.Dead{}}), KL.lefts.dead(rest)) == Nat.add(KernelLocal.dead_one(KL.Left{KL.Aside{}, KL.Dead{}}), _) : Nat}
              {==}
            case KL.Foreign{} KL.Alive{}:
              %kt.dead(rest) : {Nat.add(KL.dead(KL.Left{KL.Foreign{}, KL.Alive{}}), KL.lefts.dead(rest)) == Nat.add(KernelLocal.dead_one(KL.Left{KL.Foreign{}, KL.Alive{}}), _) : Nat}
              {==}
            case KL.Foreign{} KL.Dead{}:
              %kt.dead(rest) : {Nat.add(KL.dead(KL.Left{KL.Foreign{}, KL.Dead{}}), KL.lefts.dead(rest)) == Nat.add(KernelLocal.dead_one(KL.Left{KL.Foreign{}, KL.Dead{}}), _) : Nat}
              {==}

def kt.live(ls: List<&2, KL.Left>) -> {KL.lefts.live(ls) == KernelLocal.live_spec(ls) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case l <> rest:
      match l:
        case KL.Left{k, o}:
          match k o:
            case KL.Cand{} KL.Alive{}:
              %kt.live(rest) : {Nat.add(KL.live(KL.Left{KL.Cand{}, KL.Alive{}}), KL.lefts.live(rest)) == Nat.add(Nat.sub(1n, KernelLocal.dead_one(KL.Left{KL.Cand{}, KL.Alive{}})), _) : Nat}
              {==}
            case KL.Cand{} KL.Dead{}:
              %kt.live(rest) : {Nat.add(KL.live(KL.Left{KL.Cand{}, KL.Dead{}}), KL.lefts.live(rest)) == Nat.add(Nat.sub(1n, KernelLocal.dead_one(KL.Left{KL.Cand{}, KL.Dead{}})), _) : Nat}
              {==}
            case KL.Aside{} KL.Alive{}:
              %kt.live(rest) : {Nat.add(KL.live(KL.Left{KL.Aside{}, KL.Alive{}}), KL.lefts.live(rest)) == Nat.add(Nat.sub(1n, KernelLocal.dead_one(KL.Left{KL.Aside{}, KL.Alive{}})), _) : Nat}
              {==}
            case KL.Aside{} KL.Dead{}:
              %kt.live(rest) : {Nat.add(KL.live(KL.Left{KL.Aside{}, KL.Dead{}}), KL.lefts.live(rest)) == Nat.add(Nat.sub(1n, KernelLocal.dead_one(KL.Left{KL.Aside{}, KL.Dead{}})), _) : Nat}
              {==}
            case KL.Foreign{} KL.Alive{}:
              %kt.live(rest) : {Nat.add(KL.live(KL.Left{KL.Foreign{}, KL.Alive{}}), KL.lefts.live(rest)) == Nat.add(Nat.sub(1n, KernelLocal.dead_one(KL.Left{KL.Foreign{}, KL.Alive{}})), _) : Nat}
              {==}
            case KL.Foreign{} KL.Dead{}:
              %kt.live(rest) : {Nat.add(KL.live(KL.Left{KL.Foreign{}, KL.Dead{}}), KL.lefts.live(rest)) == Nat.add(Nat.sub(1n, KernelLocal.dead_one(KL.Left{KL.Foreign{}, KL.Dead{}})), _) : Nat}
              {==}

def KernelLocal.kernel_sweep_terms_exact(ls):
  +ms = ls
  (kt.sweep(ms), kt.dead(ms), kt.live(ms))
