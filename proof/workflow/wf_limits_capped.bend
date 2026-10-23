# eukhe: the proof of LAW wf_limits_capped

import Base
import ../../bend/workflow.bend as W
import ../../LAWS.bend as Laws

def pw.capped_succ(b: Bool, a: Nat, c: Nat) -> {W.capped(b, 1n+a, 1n+c) == 1n+W.capped(b, a, c) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pw.capped_min(a: Nat, c: Nat) -> {W.capped(Nat.is_le(a, c), a, c) == Laws.wf_min(a, c) : Nat}:
  match a c:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n++x 1n++y:
      Equal.trans(Nat, W.capped(Nat.is_le(x, y), 1n+x, 1n+y), 1n+W.capped(Nat.is_le(x, y), x, y), 1n+Laws.wf_min(x, y), pw.capped_succ(Nat.is_le(x, y), x, y), Equal.cong(Nat, Nat, n => 1n+n, W.capped(Nat.is_le(x, y), x, y), Laws.wf_min(x, y), pw.capped_min(x, y)))

def pw.capped(+c: Nat, m: Nat, +x: Nat) -> {W.effective(W.Limits{c, m}, 1n+x) == W.Limits{Laws.wf_min(c, 1n+x), m} : W.Limits}:
  %Equal.sym(Nat, W.capped(Nat.is_le(c, 1n+x), c, 1n+x), Laws.wf_min(c, 1n+x), pw.capped_min(c, 1n+x)) : {W.Limits{_, m} == W.Limits{Laws.wf_min(c, 1n+x), m} : W.Limits}
  {==}

def Laws.wf_limits_capped(c, m, x):
  pw.capped(c, m, x)
