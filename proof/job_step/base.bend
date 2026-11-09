# eukhe: lemmas of the job step laws (laws/job_step.bend)

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../base/logic/logic.bend as LLogicLogic

# min(n, m) is m when m <= n
def js.min_ge(n: Nat, m: Nat, h: {Nat.is_le(m, n) == True{} : Bool}) -> {m == Nat.min(n, m) : Nat}:
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+mp:
      LLogicLogic.pj.absurdF({1n+mp == Nat.min(0n, 1n+mp) : Nat}, h)
    case 1n+np 0n:
      {==}
    case 1n+np 1n+mp:
      %js.min_ge(np, mp, h) : {1n+mp == 1n+_ : Nat}
      {==}

# min(n, 0) is 0
def js.min_zero(n: Nat) -> {0n == Nat.min(n, 0n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def js.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def js.lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      js.le0(b)
    case 1n+ap 0n:
      LLogicLogic.pj.absurdF({Nat.is_le(1n+ap, 0n) == True{} : Bool}, h)
    case 1n+ap 1n+bp:
      js.lt_le(ap, bp, h)

# c - k is at most n when c < k + n
def js.sub_le(k: Nat, c: Nat, +n: Nat, h: {Nat.is_lt(c, Nat.add(k, n)) == True{} : Bool}) -> {Nat.is_le(Nat.sub(c, k), n) == True{} : Bool}:
  match k c:
    case 0n 0n:
      js.le0(n)
    case 0n 1n+cp:
      js.lt_le(1n+cp, n, h)
    case 1n+kp 0n:
      js.le0(n)
    case 1n+kp 1n+cp:
      js.sub_le(kp, cp, n, h)

# c - k is 0 when c <= k
def js.sub_zero_le(c: Nat, k: Nat, h: {Nat.is_le(c, k) == True{} : Bool}) -> {0n == Nat.sub(c, k) : Nat}:
  match c k:
    case 0n _:
      {==}
    case 1n+cp 0n:
      LLogicLogic.pj.absurdF({0n == Nat.sub(1n+cp, 0n) : Nat}, h)
    case 1n+cp 1n+kp:
      js.sub_zero_le(cp, kp, h)

# k is at most k + x
def js.le_add(k: Nat, x: Nat) -> {Nat.is_le(k, Nat.add(k, x)) == True{} : Bool}:
  match k:
    case 0n:
      js.le0(x)
    case 1n+p:
      js.le_add(p, x)

# Bools
# -----

def js.and_t(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def js.or_t(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def js.and_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Rust's loop over the job entry
# ------------------------------

# an ended job stays as it ended
def js.fed_ended(es: List<&2, Jb.JEv>, +t: Nat, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +x: Jb.End) -> {Jb.Ended{k, d, x} == JobStep.fed(es, t, cap, Jb.Ended{k, d, x}) : Jb.J}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      js.fed_ended(rest, t, cap, k, d, x)

# an ended job reports no more ends
def js.fed_ends_ended(es: List<&2, Jb.JEv>, +t: Nat, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +x: Jb.End) -> {Nil{} == JobStep.fed_ends(es, t, cap, Jb.Ended{k, d, x}) : List<&2, Jb.End>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      js.fed_ends_ended(rest, t, cap, k, d, x)
