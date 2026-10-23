# eukhe: lemmas the proofs of area cron share: nat

import Base
import ../../../bend/cron.bend as Cr
import ./bool.bend as LABool

def cron.pc.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pc.lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      cron.pc.le_zero(b)
    case 1n+p 0n:
      LABool.cron.pc.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pc.lt_le(p, q, h)

def pc.lt_succ_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      LABool.cron.pc.absurdF({Nat.is_le(1n+a, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      cron.pc.le_zero(q)
    case 1n+p 1n+q:
      pc.lt_succ_le(p, q, h)

# x <= c gives x <= c + d
def cron.pc.le_add(x: Nat, c: Nat, +d: Nat, h: {Nat.is_le(x, c) == True{} : Bool}) -> {Nat.is_le(x, Nat.add(c, d)) == True{} : Bool}:
  match x c:
    case 0n _:
      cron.pc.le_zero(Nat.add(c, d))
    case 1n+p 0n:
      LABool.cron.pc.absurdF({Nat.is_le(1n+p, Nat.add(0n, d)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      cron.pc.le_add(p, q, d, h)

# x <= c gives x < c + 1 + k
def pc.lt_add(x: Nat, c: Nat, +k: Nat, h: {Nat.is_le(x, c) == True{} : Bool}) -> {Nat.is_lt(x, Nat.add(c, 1n+k)) == True{} : Bool}:
  match x c:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LABool.cron.pc.absurdF({Nat.is_lt(1n+p, Nat.add(0n, 1n+k)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pc.lt_add(p, q, k, h)

def cron.pc.eq_refl(k: Nat) -> {Nat.is_eq(k, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cron.pc.eq_refl(p)

def cron.pc.eq_of(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LABool.cron.pc.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LABool.cron.pc.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      +e = cron.pc.eq_of(p, q, h)
      %e : {1n+p == 1n+_ : Nat}
      {==}

def pc.Below(+x: Nat, nx: Maybe<&2, Nat>) -> Type:
  match nx:
    case None{}:
      Unit
    case Some{n}:
      {Nat.is_lt(x, n) == True{} : Bool}

def pc.eq_flip(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      h
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pc.eq_flip(p, q, h)

# The finish step keeps the invariant
# -----------------------------------

# a pause lies after the clock: x <= c gives x < c + delay(k)
def pc.lt_delay(+x: Nat, +c: Nat, k: Nat, +le: {Nat.is_le(x, c) == True{} : Bool}) -> {Nat.is_lt(x, Nat.add(c, Cr.delay(k))) == True{} : Bool}:
  match k:
    case 0n:
      pc.lt_add(x, c, 1n, le)
    case 1n+a:
      match a:
        case 0n:
          pc.lt_add(x, c, 1n, le)
        case 1n+b:
          match b:
            case 0n:
              pc.lt_add(x, c, 3n, le)
            case 1n+d:
              match d:
                case 0n:
                  pc.lt_add(x, c, 7n, le)
                case 1n+e:
                  match e:
                    case 0n:
                      pc.lt_add(x, c, 15n, le)
                    case 1n+f:
                      match f:
                        case 0n:
                          pc.lt_add(x, c, 31n, le)
                        case 1n+g:
                          pc.lt_add(x, c, 59n, le)

def pc.lt_pick(b: Bool, +n: Nat, +u: Nat, +x: Nat, ltu: {Nat.is_lt(x, u) == True{} : Bool}, ltn: {Nat.is_lt(x, n) == True{} : Bool}) -> {Nat.is_lt(x, Cr.later.pick(b, n, u)) == True{} : Bool}:
  match b:
    case True{}:
      ltu
    case False{}:
      ltn

# the next run after a failure lies after every start
def pc.lt_later(+nx: Maybe<&2, Nat>, +x: Nat, +u: Nat, ltu: {Nat.is_lt(x, u) == True{} : Bool}, bl: pc.Below(x, nx)) -> {Nat.is_lt(x, Cr.later(nx, u)) == True{} : Bool}:
  match nx:
    case None{}:
      ltu
    case Some{+n}:
      pc.lt_pick(Nat.is_lt(n, u), n, u, x, ltu, bl)

def pc.top_fail2(+x: Nat, +c: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +a: {Nat.is_le(x, c) == True{} : Bool}, bl: pc.Below(x, nx)) -> ({Nat.is_le(x, c) == True{} : Bool} & pc.Below(x, Some{Cr.later(nx, Nat.add(c, Cr.delay(k)))})):
  (a, pc.lt_later(nx, x, Nat.add(c, Cr.delay(k)), pc.lt_delay(x, c, k, a), bl))
