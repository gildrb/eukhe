# eukhe: the proof of LAW task_life_join_may_run
#
# PROOF: by induction on the live flags, the join's "no live flag set"
# (not any) is "no flag counted" (tlj.any_count); every mark list the
# join builds (keep_all, abort_others) has one mark per live flag
# (tlj.len_keep, tlj.len_ao, by induction).

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ./base.bend as LB

def tlj.any_count(xs: List<&2, Bool>) -> {Bool.not(Tl.any(xs)) == Nat.is_eq(Sp.count(xs), 0n) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case True{}:
          {==}
        case False{}:
          tlj.any_count(t)

def tlj.len_keep(xs: List<&2, Bool>) -> {List.length(&2, Bool, Tl.keep_all(xs)) == List.length(&2, Bool, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %tlj.len_keep(t) : {1n+List.length(&2, Bool, Tl.keep_all(t)) == 1n+_ : Nat}
      {==}

def tlj.len_ao(xs: List<&2, Bool>, fs: List<&2, Bool>) -> {List.length(&2, Bool, Tl.abort_others(xs, fs)) == List.length(&2, Bool, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match fs:
        case Nil{}:
          %tlj.len_ao(t, Nil{}) : {1n+List.length(&2, Bool, Tl.abort_others(t, Nil{})) == 1n+_ : Nat}
          {==}
        case f <> u:
          %tlj.len_ao(t, u) : {1n+List.length(&2, Bool, Tl.abort_others(t, u)) == 1n+_ : Nat}
          {==}

def tlj.len_marks(p: Tl.Policy, b: Bool, +xs: List<&2, Bool>, fs: List<&2, Bool>) -> {List.length(&2, Bool, Tl.join.marks(p, b, xs, fs)) == List.length(&2, Bool, xs) : Nat}:
  match p:
    case Tl.FailFast{}:
      match b:
        case True{}:
          tlj.len_ao(xs, fs)
        case False{}:
          tlj.len_keep(xs)
    case Tl.AllSettled{}:
      tlj.len_keep(xs)

def TaskLife.task_life_join_may_run(p, live, failed):
  (tlj.any_count(live), tlj.len_marks(p, Tl.any(failed), live, failed))
