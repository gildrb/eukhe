# eukhe: lemmas the proofs of area cron share: nat

import Base
import ../../../bend/cron.bend as Cr
import ./logic.bend as LALogic

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
      LALogic.cron.pc.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pc.lt_le(p, q, h)

def pc.lt_succ_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      LALogic.cron.pc.absurdF({Nat.is_le(1n+a, 0n) == True{} : Bool}, h)
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
      LALogic.cron.pc.absurdF({Nat.is_le(1n+p, Nat.add(0n, d)) == True{} : Bool}, h)
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
      LALogic.cron.pc.absurdF({Nat.is_lt(1n+p, Nat.add(0n, 1n+k)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pc.lt_add(p, q, k, h)

def cron.pc.eq_refl(k: Nat) -> {Nat.is_eq(k, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cron.pc.eq_refl(p)

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
def pc.lt_later(+nx: Maybe<&2, Nat>, +x: Nat, +u: Nat, ltu: {Nat.is_lt(x, u) == True{} : Bool}, bl: LALogic.pc.Below(x, nx)) -> {Nat.is_lt(x, Cr.later(nx, u)) == True{} : Bool}:
  match nx:
    case None{}:
      ltu
    case Some{+n}:
      pc.lt_pick(Nat.is_lt(n, u), n, u, x, ltu, bl)

def pc.top_fail2(+x: Nat, +c: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +a: {Nat.is_le(x, c) == True{} : Bool}, bl: LALogic.pc.Below(x, nx)) -> ({Nat.is_le(x, c) == True{} : Bool} & LALogic.pc.Below(x, Some{Cr.later(nx, Nat.add(c, Cr.delay(k)))})):
  (a, pc.lt_later(nx, x, Nat.add(c, Cr.delay(k)), pc.lt_delay(x, c, k, a), bl))

def pc.top_tick(+ss: List<&2, Nat>, +c: Nat, +d: Nat, -nx: Maybe<&2, Nat>, t: LALogic.pc.Top(ss, c, nx)) -> LALogic.pc.Top(ss, Nat.add(c, d), nx):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> +u:
      (a, b) = t
      (cron.pc.le_add(x, c, d, a), b)

# an active job's count holds for any status
def pc.cnt_down(+st: Cr.Status, +k: Nat, +h: List<&2, Cr.Mark>, c6: LALogic.pc.Cnt(Cr.Active{}, k, h)) -> LALogic.pc.Cnt(st, k, h):
  match st:
    case Cr.Active{}:
      c6
    case Cr.Paused{}:
      (ek, lt) = c6
      (ek, pc.lt_le(k, Cr.CAP(), lt))
    case Cr.Finished{}:
      (ek, lt) = c6
      (ek, pc.lt_le(k, Cr.CAP(), lt))
    case Cr.Cancelled{}:
      (ek, lt) = c6
      (ek, pc.lt_le(k, Cr.CAP(), lt))

def pc.g_tick(+c: Nat, +d: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: LALogic.pc.G(c, dead, j)) -> LALogic.pc.G(Nat.add(c, d), dead, j):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h1, (h2, (h3, (pc.top_tick(ss, c, d, nx, h4), g5))))

def pc.all_tick(+c: Nat, +d: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, g: LALogic.pc.AllG(c, dead, rs)) -> LALogic.pc.AllG(Nat.add(c, d), dead, rs):
  match rs:
    case Nil{}:
      Unit{}
    case r <> t:
      match r:
        case Cr.Known{+j}:
          (a, b) = g
          (pc.g_tick(c, d, dead, j, a), pc.all_tick(c, d, dead, t, b))
        case Cr.Raw{x}:
          pc.all_tick(c, d, dead, t, g)
