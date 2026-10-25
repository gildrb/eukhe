# eukhe: the proof of LAW goal_judge_exact
# The prior's stalls held below t (Nat.min with t - 1) are the spec's
# held count; the check is the spec's on each verdict.

import Base
import ../../bend/progress.bend as Pr
import ../../laws/progress.bend as Progress
import ../base/nat.bend as LNat

def gje.put(b: Bool, n: Nat) -> {Pr.strike.put(b, n) == Progress.gj_stall.at(b, n) : Pr.Goal}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gje.check(g: Bool, +cap: Nat, +n: Nat) -> {Pr.check(cap, n, g) == Progress.gj_grew(g, cap, n) : Pr.Goal}:
  match g:
    case True{}:
      {==}
    case False{}:
      gje.put(Nat.is_le(cap, 1n+n), 1n+n)

def gje.at_succ(b: Bool, sp: Nat, +q: Nat) -> {1n+Progress.gj_held.at(b, sp, 1n+q) == Progress.gj_held.at(b, 1n+sp, 2n+q) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gje.zero(sp: Nat) -> {0n == Progress.gj_held.at(Nat.is_lt(sp, 0n), 1n+sp, 1n) : Nat}:
  match sp:
    case 0n:
      {==}
    case 1n+k:
      {==}

# min(s, u) is s held below 1 + u
def gje.held1(s: Nat, u: Nat) -> {Nat.min(s, u) == Progress.gj_held(1n+u, s) : Nat}:
  match s u:
    case 0n _:
      {==}
    case 1n+sp 0n:
      gje.zero(sp)
    case 1n++sp 1n++q:
      +b = Nat.is_lt(sp, 1n+q)
      Equal.trans(Nat, 1n+Nat.min(sp, q), 1n+Progress.gj_held.at(b, sp, 1n+q), Progress.gj_held.at(b, 1n+sp, 2n+q), Equal.cong(Nat, Nat, n => 1n+n, Nat.min(sp, q), Progress.gj_held.at(b, sp, 1n+q), gje.held1(sp, q)), gje.at_succ(b, sp, q))

# min(s, t - 1) is s held below t
def gje.held(t: Nat, +s: Nat) -> {Nat.min(s, Nat.sub(t, 1n)) == Progress.gj_held(t, s) : Nat}:
  match t:
    case 0n:
      match s:
        case 0n:
          {==}
        case 1n+sp:
          {==}
    case 1n++u:
      Equal.trans(Nat, Nat.min(s, Nat.sub(u, 0n)), Nat.min(s, u), Progress.gj_held(1n+u, s), Equal.cong(Nat, Nat, v => Nat.min(s, v), Nat.sub(u, 0n), u, Equal.sym(Nat, u, Nat.sub(u, 0n), LNat.pj.sub_zero(u))), gje.held1(s, u))

def Progress.goal_judge_exact(t, cap, p, work):
  match p:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Pr.Prior{+s, +w}:
          +g = Nat.is_lt(w, work)
          +n = Progress.gj_held(t, s)
          Equal.trans(Pr.Goal, Pr.check(cap, Nat.min(s, Nat.sub(t, 1n)), g), Pr.check(cap, n, g), Progress.gj_grew(g, cap, n), Equal.cong(Nat, Pr.Goal, v => Pr.check(cap, v, g), Nat.min(s, Nat.sub(t, 1n)), n, gje.held(t, s)), gje.check(g, cap, n))
