# eukhe: the proof of LAW job_rewind_refines
# Job by job, the job at place i: the model's held is the laws' held (a
# commit below the target is one the target is not at or below); the
# tree holds the job (its id i heads the ids held, and no later slot has
# id i, so the head id changes nothing after it) or not (no id held from
# i + 1 on is i).

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ../base/nat.bend as LNat

def pr.not_le(t: Nat, a: Nat) -> {Nat.is_lt(a, t) == Bool.not(Nat.is_le(t, a)) : Bool}:
  match t a:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pr.not_le(p, q)

def pr.held(target: Maybe<&2, Nat>, a: Maybe<&2, Nat>) -> {Jb.held(target, a) == Job.rw_held_spec(target, a) : Bool}:
  match target a:
    case None{} None{}:
      {==}
    case None{} Some{x}:
      {==}
    case Some{t} None{}:
      {==}
    case Some{t} Some{x}:
      pr.not_le(t, x)

def pr.ne(+x: Nat, +j: Nat, lt: {Nat.is_lt(x, j) == True{} : Bool}) -> {False{} == Nat.is_eq(x, j) : Bool}:
  Equal.sym(Bool, Nat.is_eq(x, j), False{}, LNat.pt.lt_ne(x, j, lt))

def pr.ne_r(+x: Nat, +j: Nat, lt: {Nat.is_lt(x, j) == True{} : Bool}) -> {False{} == Nat.is_eq(j, x) : Bool}:
  Equal.sym(Bool, Nat.is_eq(j, x), False{}, LNat.pt.lt_ne_r(x, j, lt))

def pr.refl(i: Nat) -> {True{} == Nat.is_eq(i, i) : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      pr.refl(p)

# an id below every slot's id held in front changes no slot
def pr.drop(xs: List<&2, Jb.Seen>, +j: Nat, +x: Nat, -K: List<&2, Nat>, +lt: {Nat.is_lt(x, j) == True{} : Bool}) -> {Jb.rewind(Job.rw_slots(xs, j), K) == Jb.rewind(Job.rw_slots(xs, j), x <> K) : List<&2, Jb.Slot>}:
  match xs:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Jb.Seen{r, a}:
          %pr.ne(x, j, lt) : {Jb.stop.at(Jb.elem(K, j), Jb.Slot{j, r}) <> Jb.rewind(Job.rw_slots(rest, 1n+j), K) == Jb.stop.at(Bool.or(_, Jb.elem(K, j)), Jb.Slot{j, r}) <> Jb.rewind(Job.rw_slots(rest, 1n+j), x <> K) : List<&2, Jb.Slot>}
          %pr.drop(rest, 1n+j, x, K, LNat.rp.lt_succ(x, j, lt)) : {Jb.stop.at(Jb.elem(K, j), Jb.Slot{j, r}) <> Jb.rewind(Job.rw_slots(rest, 1n+j), K) == Jb.stop.at(Jb.elem(K, j), Jb.Slot{j, r}) <> _ : List<&2, Jb.Slot>}
          {==}

def pr.not_held_at(h: Bool, +j: Nat, +x: Nat, -L: List<&2, Nat>, ih: {False{} == Jb.elem(L, x) : Bool}, ne: {False{} == Nat.is_eq(j, x) : Bool}) -> {False{} == Jb.elem(Job.rw_put_if(h, j, L), x) : Bool}:
  match h:
    case True{}:
      %ne : {False{} == Bool.or(_, Jb.elem(L, x)) : Bool}
      ih
    case False{}:
      ih

# no id held from j on is below j
def pr.not_held(xs: List<&2, Jb.Seen>, +t: Maybe<&2, Nat>, +j: Nat, +x: Nat, +lt: {Nat.is_lt(x, j) == True{} : Bool}) -> {False{} == Jb.elem(Job.rw_held_ids(xs, t, j), x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Jb.Seen{r, a}:
          pr.not_held_at(Job.rw_held_spec(t, a), j, x, Job.rw_held_ids(rest, t, 1n+j), pr.not_held(rest, t, 1n+j, x, LNat.rp.lt_succ(x, j, lt)), pr.ne_r(x, j, lt))

# a running job: held, it stays; else it stops
def pr.step_run(h: Bool, +i: Nat, -S: List<&2, Jb.Slot>, -KS: List<&2, Bool>, -K: List<&2, Nat>,
  ih: {Job.rw_stopped(S, KS) == Jb.rewind(S, K) : List<&2, Jb.Slot>},
  drop: {Jb.rewind(S, K) == Jb.rewind(S, i <> K) : List<&2, Jb.Slot>},
  miss: {False{} == Jb.elem(K, i) : Bool},
  refl: {True{} == Nat.is_eq(i, i) : Bool})
  -> {Job.rw_stop_if(Bool.not(h), Jb.Slot{i, True{}}) <> Job.rw_stopped(S, KS) == Jb.stop.at(Jb.elem(Job.rw_put_if(h, i, K), i), Jb.Slot{i, True{}}) <> Jb.rewind(S, Job.rw_put_if(h, i, K)) : List<&2, Jb.Slot>}:
  match h:
    case True{}:
      %refl : {Jb.Slot{i, True{}} <> Job.rw_stopped(S, KS) == Jb.stop.at(Bool.or(_, Jb.elem(K, i)), Jb.Slot{i, True{}}) <> Jb.rewind(S, i <> K) : List<&2, Jb.Slot>}
      %drop : {Jb.Slot{i, True{}} <> Job.rw_stopped(S, KS) == Jb.Slot{i, True{}} <> _ : List<&2, Jb.Slot>}
      %ih : {Jb.Slot{i, True{}} <> Job.rw_stopped(S, KS) == Jb.Slot{i, True{}} <> _ : List<&2, Jb.Slot>}
      {==}
    case False{}:
      %miss : {Jb.Slot{i, False{}} <> Job.rw_stopped(S, KS) == Jb.stop.at(_, Jb.Slot{i, True{}}) <> Jb.rewind(S, K) : List<&2, Jb.Slot>}
      %ih : {Jb.Slot{i, False{}} <> Job.rw_stopped(S, KS) == Jb.Slot{i, False{}} <> _ : List<&2, Jb.Slot>}
      {==}

# an ended job stays ended, held or not
def pr.step_ended(h: Bool, +i: Nat, -S: List<&2, Jb.Slot>, -KS: List<&2, Bool>, -K: List<&2, Nat>,
  ih: {Job.rw_stopped(S, KS) == Jb.rewind(S, K) : List<&2, Jb.Slot>},
  drop: {Jb.rewind(S, K) == Jb.rewind(S, i <> K) : List<&2, Jb.Slot>},
  miss: {False{} == Jb.elem(K, i) : Bool},
  refl: {True{} == Nat.is_eq(i, i) : Bool})
  -> {Job.rw_stop_if(False{}, Jb.Slot{i, False{}}) <> Job.rw_stopped(S, KS) == Jb.stop.at(Jb.elem(Job.rw_put_if(h, i, K), i), Jb.Slot{i, False{}}) <> Jb.rewind(S, Job.rw_put_if(h, i, K)) : List<&2, Jb.Slot>}:
  match h:
    case True{}:
      %refl : {Jb.Slot{i, False{}} <> Job.rw_stopped(S, KS) == Jb.stop.at(Bool.or(_, Jb.elem(K, i)), Jb.Slot{i, False{}}) <> Jb.rewind(S, i <> K) : List<&2, Jb.Slot>}
      %drop : {Jb.Slot{i, False{}} <> Job.rw_stopped(S, KS) == Jb.Slot{i, False{}} <> _ : List<&2, Jb.Slot>}
      %ih : {Jb.Slot{i, False{}} <> Job.rw_stopped(S, KS) == Jb.Slot{i, False{}} <> _ : List<&2, Jb.Slot>}
      {==}
    case False{}:
      %miss : {Jb.Slot{i, False{}} <> Job.rw_stopped(S, KS) == Jb.stop.at(_, Jb.Slot{i, False{}}) <> Jb.rewind(S, K) : List<&2, Jb.Slot>}
      %ih : {Jb.Slot{i, False{}} <> Job.rw_stopped(S, KS) == Jb.Slot{i, False{}} <> _ : List<&2, Jb.Slot>}
      {==}

def pr.refine(js: List<&2, Jb.Seen>, +t: Maybe<&2, Nat>, +i: Nat) -> {Job.rw_stopped(Job.rw_slots(js, i), Jb.kills(js, t)) == Jb.rewind(Job.rw_slots(js, i), Job.rw_held_ids(js, t, i)) : List<&2, Jb.Slot>}:
  match js:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Jb.Seen{r, +a}:
          match r:
            case True{}:
              +K = Job.rw_held_ids(rest, t, 1n+i)
              %pr.held(t, a) : {Job.rw_stop_if(Bool.not(Jb.held(t, a)), Jb.Slot{i, True{}}) <> Job.rw_stopped(Job.rw_slots(rest, 1n+i), Jb.kills(rest, t)) == Jb.stop.at(Jb.elem(Job.rw_put_if(_, i, K), i), Jb.Slot{i, True{}}) <> Jb.rewind(Job.rw_slots(rest, 1n+i), Job.rw_put_if(_, i, K)) : List<&2, Jb.Slot>}
              pr.step_run(Jb.held(t, a), i, Job.rw_slots(rest, 1n+i), Jb.kills(rest, t), K, pr.refine(rest, t, 1n+i), pr.drop(rest, 1n+i, i, K, LNat.rp.lt_self(i)), pr.not_held(rest, t, 1n+i, i, LNat.rp.lt_self(i)), pr.refl(i))
            case False{}:
              pr.step_ended(Job.rw_held_spec(t, a), i, Job.rw_slots(rest, 1n+i), Jb.kills(rest, t), Job.rw_held_ids(rest, t, 1n+i), pr.refine(rest, t, 1n+i), pr.drop(rest, 1n+i, i, Job.rw_held_ids(rest, t, 1n+i), LNat.rp.lt_self(i)), pr.not_held(rest, t, 1n+i, i, LNat.rp.lt_self(i)), pr.refl(i))

def Job.job_rewind_refines(js, target):
  pr.refine(js, target, 0n)
