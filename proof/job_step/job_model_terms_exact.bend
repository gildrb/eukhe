# eukhe: the proof of LAW job_model_terms_exact
# Each term by induction on its list.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep

def jmt.ticks(es: List<&2, Jb.JEv>) -> {JobStep.ticks_spec(es) == Jb.ticks(es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Jb.Out{n}:
          jmt.ticks(rest)
        case Jb.Quit{c}:
          jmt.ticks(rest)
        case Jb.Kill{}:
          jmt.ticks(rest)
        case Jb.Tick{}:
          %jmt.ticks(rest) : {1n+JobStep.ticks_spec(rest) == 1n+_ : Nat}
          {==}

def jmt.elem(xs: List<&2, Nat>, +x: Nat) -> {JobStep.elem_spec(xs, x) == Jb.elem(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> rest:
      %jmt.elem(rest, x) : {Bool.or(Nat.is_eq(y, x), JobStep.elem_spec(rest, x)) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def jmt.running(js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {JobStep.running_in_spec(js, keep) == Jb.running_in(js, keep) : Bool}:
  match js:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Jb.Slot{+i, r}:
          %jmt.elem(keep, i) : {Bool.and(Bool.or(Bool.not(r), JobStep.elem_spec(keep, i)), JobStep.running_in_spec(rest, keep)) == Bool.and(Bool.or(Bool.not(r), _), Jb.running_in(rest, keep)) : Bool}
          %jmt.running(rest, keep) : {Bool.and(Bool.or(Bool.not(r), JobStep.elem_spec(keep, i)), JobStep.running_in_spec(rest, keep)) == Bool.and(Bool.or(Bool.not(r), JobStep.elem_spec(keep, i)), _) : Bool}
          {==}

def jmt.beq(a: Bool, b: Bool) -> {JobStep.same_bool(a, b) == Jb.b.eq(a, b) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def jmt.kept(js: List<&2, Jb.Slot>, ks: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {JobStep.slots_kept_spec(js, ks, keep) == Jb.kept(js, ks, keep) : Bool}:
  match js:
    case Nil{}:
      match ks:
        case Nil{}:
          {==}
        case k <> kr:
          {==}
    case j <> jr:
      match j:
        case Jb.Slot{+i, r}:
          match ks:
            case Nil{}:
              {==}
            case k <> kr:
              match k:
                case Jb.Slot{+h, +q}:
                  %jmt.elem(keep, i) : {Bool.and(Bool.or(Bool.not(JobStep.elem_spec(keep, i)), Bool.and(Nat.is_eq(i, h), JobStep.same_bool(r, q))), JobStep.slots_kept_spec(jr, kr, keep)) == Bool.and(Bool.or(Bool.not(_), Bool.and(Nat.is_eq(i, h), Jb.b.eq(r, q))), Jb.kept(jr, kr, keep)) : Bool}
                  %jmt.beq(r, q) : {Bool.and(Bool.or(Bool.not(JobStep.elem_spec(keep, i)), Bool.and(Nat.is_eq(i, h), JobStep.same_bool(r, q))), JobStep.slots_kept_spec(jr, kr, keep)) == Bool.and(Bool.or(Bool.not(JobStep.elem_spec(keep, i)), Bool.and(Nat.is_eq(i, h), _)), Jb.kept(jr, kr, keep)) : Bool}
                  %jmt.kept(jr, kr, keep) : {Bool.and(Bool.or(Bool.not(JobStep.elem_spec(keep, i)), Bool.and(Nat.is_eq(i, h), JobStep.same_bool(r, q))), JobStep.slots_kept_spec(jr, kr, keep)) == Bool.and(Bool.or(Bool.not(JobStep.elem_spec(keep, i)), Bool.and(Nat.is_eq(i, h), JobStep.same_bool(r, q))), _) : Bool}
                  {==}

def JobStep.job_model_terms_exact(es, xs, x, js, ks, keep):
  (Equal.sym(Nat, JobStep.ticks_spec(es), Jb.ticks(es), jmt.ticks(es)), (Equal.sym(Bool, JobStep.elem_spec(xs, x), Jb.elem(xs, x), jmt.elem(xs, x)), (Equal.sym(Bool, JobStep.running_in_spec(js, keep), Jb.running_in(js, keep), jmt.running(js, keep)), Equal.sym(Bool, JobStep.slots_kept_spec(js, ks, keep), Jb.kept(js, ks, keep), jmt.kept(js, ks, keep)))))
