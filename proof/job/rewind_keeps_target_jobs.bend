# eukhe: the proof of LAW rewind_keeps_target_jobs

import Base
import ../../bend/job.bend as Jb
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pj.beq_refl(r: Bool) -> {True{} == Jb.b.eq(r, r) : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

def pj.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pj.eq_refl(p)

def pj.ok_keep(h: Bool, +i: Nat, +r: Bool) -> {True{} == Bool.or(Bool.not(h), Bool.and(Nat.is_eq(i, i), Jb.b.eq(Jb.Slot.running(Jb.stop.at(h, Jb.Slot{i, r})), r))) : Bool}:
  match h:
    case True{}:
      %pj.eq_refl(i) : {True{} == Bool.and(_, Jb.b.eq(r, r)) : Bool}
      pj.beq_refl(r)
    case False{}:
      {==}

def pj.keeps(js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.kept(Jb.rewind(js, keep), js, keep) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Jb.Slot{+i, +r}:
          +h = Jb.elem(keep, i)
          +S = Jb.stop.at(h, Jb.Slot{i, r})
          %LA.pj.id_stop(h, i, r) : {Bool.and(Bool.or(Bool.not(Jb.elem(keep, _)), Bool.and(Nat.is_eq(_, i), Jb.b.eq(Jb.Slot.running(S), r))), Jb.kept(Jb.rewind(rest, keep), rest, keep)) == True{} : Bool}
          %pj.ok_keep(h, i, r) : {Bool.and(_, Jb.kept(Jb.rewind(rest, keep), rest, keep)) == True{} : Bool}
          pj.keeps(rest, keep)

def pj.rewind_keeps_target_jobs(+js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.kept(Jb.rewind(js, keep), js, keep) == True{} : Bool}:
  pj.keeps(js, keep)

def Laws.rewind_keeps_target_jobs(js, keep):
  pj.rewind_keeps_target_jobs(js, keep)
