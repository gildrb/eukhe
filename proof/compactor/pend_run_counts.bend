# eukhe: the proof of LAW pend_run_counts
# Induction on the outcomes, over the failures left: a built line stays
# built (prc.made); a saved line builds; a failure with none left builds
# (more failures than left: the count says so too), with some left it
# counts one down (prc.down: one failure fewer on both sides); a disk
# error and a stop change neither the line nor the counts.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

def prc.made(os: List<&2, C.Outcome>) -> {C.Pend.run(os, C.Made{}) == C.Made{} : C.Pend}:
  match os:
    case Nil{}:
      {==}
    case o <> rest:
      match o:
        case C.Built{}:
          prc.made(rest)
        case C.Failed{}:
          prc.made(rest)
        case C.Disk{}:
          prc.made(rest)
        case C.Stopped{}:
          prc.made(rest)

def prc.or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def prc.down(b: Bool, -m: Nat, -f: Nat) -> {Compactor.owed_after(b, m, f) == Compactor.owed_after(b, 1n+m, 1n+f) : C.Pend}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def prc.owed(os: List<&2, C.Outcome>, +n: Nat) -> {C.Pend.run(os, C.Owed{n}) == Compactor.after_all(os, C.Owed{n}) : C.Pend}:
  match os:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          {==}
    case o <> +rest:
      match o:
        case C.Built{}:
          prc.made(rest)
        case C.Failed{}:
          match n:
            case 0n:
              %Equal.sym(Bool, Bool.or(Compactor.saved(rest), True{}), True{}, prc.or_true(Compactor.saved(rest))) : {C.Pend.run(rest, C.Made{}) == Compactor.owed_after(_, 0n, 1n+Compactor.failures(rest)) : C.Pend}
              prc.made(rest)
            case 1n+m:
              +f = Compactor.failures(rest)
              Equal.trans(C.Pend, C.Pend.run(rest, C.Owed{m}), Compactor.owed_after(Bool.or(Compactor.saved(rest), Nat.is_lt(m, f)), m, f), Compactor.owed_after(Bool.or(Compactor.saved(rest), Nat.is_lt(m, f)), 1n+m, 1n+f), prc.owed(rest, m), prc.down(Bool.or(Compactor.saved(rest), Nat.is_lt(m, f)), m, f))
        case C.Disk{}:
          prc.owed(rest, n)
        case C.Stopped{}:
          prc.owed(rest, n)

def Compactor.pend_run_counts(os, p):
  match p:
    case C.Made{}:
      prc.made(os)
    case C.Owed{n}:
      prc.owed(os, n)
