# eukhe: lemmas of the cron_job proofs
# The model's small terms equal the specs' terms the per-job specs read:
# membership, a process left out of the runs, the failure pause, the later
# of a next run and a pause end.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_terms.bend as CronTerms
import ../../laws/cron_step.bend as CronStep

def cj.has(+p: Nat, xs: List<&2, Nat>) -> {Cr.has(p, xs) == CronTerms.has_spec(p, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %cj.has(p, t) : {Bool.or(Nat.is_eq(x, p), Cr.has(p, t)) == Bool.or(Nat.is_eq(x, p), _) : Bool}
      {==}

def cj.keep(b: Bool, x: Nat, r: List<&2, Nat>) -> {Cr.drop.put(b, x, r) == CronStep.keep_run_spec(b, x, r) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cj.drop(+p: Nat, xs: List<&2, Nat>) -> {Cr.drop(p, xs) == CronStep.drop_spec(p, xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %cj.drop(p, t) : {Cr.drop.put(Nat.is_eq(x, p), x, Cr.drop(p, t)) == CronStep.keep_run_spec(Nat.is_eq(x, p), x, _) : List<&2, Nat>}
      cj.keep(Nat.is_eq(x, p), x, Cr.drop(p, t))

def cj.delay(k: Nat) -> {Cr.delay(k) == CronTerms.delay_spec(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      match e:
                        case 0n:
                          {==}
                        case 1n+f:
                          {==}

def cj.pick_succ(b: Bool, +p: Nat, +q: Nat) -> {Cr.later.pick(b, 1n+p, 1n+q) == 1n+Cr.later.pick(b, p, q) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cj.max(n: Nat, u: Nat) -> {Cr.later.pick(Nat.is_lt(n, u), n, u) == Nat.max(n, u) : Nat}:
  match n u:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+(+p) 1n+(+q):
      %Equal.sym(Nat, Cr.later.pick(Nat.is_lt(p, q), 1n+p, 1n+q), 1n+Cr.later.pick(Nat.is_lt(p, q), p, q), cj.pick_succ(Nat.is_lt(p, q), p, q)) : {_ == 1n+Nat.max(p, q) : Nat}
      %cj.max(p, q) : {1n+Cr.later.pick(Nat.is_lt(p, q), p, q) == 1n+_ : Nat}
      {==}

def cj.later(nx: Maybe<&2, Nat>, +u: Nat) -> {Cr.later(nx, u) == CronTerms.later_spec(nx, u) : Nat}:
  match nx:
    case None{}:
      {==}
    case Some{n}:
      cj.max(n, u)
