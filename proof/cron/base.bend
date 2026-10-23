# eukhe: lemmas the proofs of area cron share

import Base
import ../../bend/cron.bend as Cr
import ../../LAWS.bend as Laws

# ---- cron ----

# proof_cron: the cron laws of LAWS.bend section cron (D2). Every event keeps an
# invariant of the reachable states, job by job (`pc.G`): at most one
# process runs a job, its run holds the claim on record and its process
# is alive; the occurrences that started fall strictly and lie at or
# before the clock and before the next run; a one-shot that started has
# no next run; the failures in a row match the job's counted results and
# stay under the cap while the job is active; a finished one-shot has no
# run. From it: `cron_fires_once`, `cron_once_finished_after_end` and the
# first part of `cron_backoff_bounded`. The other laws are about one step
# from any state: `cron_never_drops`, `cron_claim_owned`, and the rest of
# `cron_backoff_bounded`.

# Logic and numbers
# -----------------

def cron.pc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def cron.pc.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : cron.pc.BD(_, Unit, A)
  Unit{}

def cron.pc.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : cron.pc.BD(_, A, Unit)
  Unit{}

def cron.pc.MD(m: Maybe<&2, Nat>, A: Type) -> Type:
  match m:
    case None{}:
      A
    case Some{x}:
      Unit

def pc.some_none(-A: Type, -x: Nat, e: {Some{x} == None{} : Maybe<&2, Nat>}) -> A:
  %e : cron.pc.MD(_, A)
  Unit{}

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
      cron.pc.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pc.lt_le(p, q, h)

def pc.lt_succ_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      cron.pc.absurdF({Nat.is_le(1n+a, 0n) == True{} : Bool}, h)
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
      cron.pc.absurdF({Nat.is_le(1n+p, Nat.add(0n, d)) == True{} : Bool}, h)
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
      cron.pc.absurdF({Nat.is_lt(1n+p, Nat.add(0n, 1n+k)) == True{} : Bool}, h)
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
      cron.pc.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      cron.pc.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      +e = cron.pc.eq_of(p, q, h)
      %e : {1n+p == 1n+_ : Nat}
      {==}

# The invariant of a job
# ----------------------

# the processes that run the job are alive
def pc.Live(rs: List<&2, Nat>, +dead: List<&2, Nat>) -> Type:
  match rs:
    case Nil{}:
      Unit
    case +o <> t:
      ({Cr.has(o, dead) == False{} : Bool} & pc.Live(t, dead))

def pc.Below(+x: Nat, nx: Maybe<&2, Nat>) -> Type:
  match nx:
    case None{}:
      Unit
    case Some{n}:
      {Nat.is_lt(x, n) == True{} : Bool}

# the newest occurrence that started is at or before the clock and
# before the next run
def pc.Top(ss: List<&2, Nat>, +c: Nat, +nx: Maybe<&2, Nat>) -> Type:
  match ss:
    case Nil{}:
      Unit
    case +x <> t:
      ({Nat.is_le(x, c) == True{} : Bool} & pc.Below(x, nx))

# a one-shot that started has no next run
def pc.OnceG(s: Cr.Sched, ss: List<&2, Nat>, +nx: Maybe<&2, Nat>) -> Type:
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          Unit
        case x <> t:
          ({t == Nil{} : List<&2, Nat>} & {nx == None{} : Maybe<&2, Nat>})
    case Cr.Every{q}:
      Unit

def pc.Act2(st: Cr.Status, +k: Nat) -> Data:
  match st:
    case Cr.Active{}:
      {Nat.is_lt(k, Cr.CAP()) == True{} : Bool}
    case Cr.Paused{}:
      {Nat.is_le(k, Cr.CAP()) == True{} : Bool}
    case Cr.Finished{}:
      {Nat.is_le(k, Cr.CAP()) == True{} : Bool}
    case Cr.Cancelled{}:
      {Nat.is_le(k, Cr.CAP()) == True{} : Bool}

# the failures in a row are the counted ones, under the cap while active
def pc.Cnt(+st: Cr.Status, +k: Nat, +h: List<&2, Cr.Mark>) -> Type:
  ({k == Cr.trail(h) : Nat} & pc.Act2(st, k))

def pc.G(+c: Nat, +dead: List<&2, Nat>, j: Cr.Job) -> Type:
  match j:
    case Cr.Job{i, +s, +st, +nx, k, cl, +rs, +ss, h}:
      (Cr.Held(rs, cl) & (pc.Live(rs, dead) & (Cr.Desc(ss) & (pc.Top(ss, c, nx) & (pc.OnceG(s, ss, nx) & (pc.Cnt(st, k, h) & Cr.EndsOf(s, st, rs)))))))

def pc.AllG(+c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>) -> Type:
  match rs:
    case Nil{}:
      Unit
    case r <> t:
      match r:
        case Cr.Known{j}:
          (pc.G(c, dead, j) & pc.AllG(c, dead, t))
        case Cr.Raw{x}:
          pc.AllG(c, dead, t)

def pc.Inv(s: Cr.S) -> Type:
  match s:
    case Cr.S{b, rs, rd, dead, c, n, a}:
      pc.AllG(c, dead, rs)

# A claim keeps the invariant
# ---------------------------

# a next run rolled from c lies after every occurrence at or before c
def pc.below_adv(+s: Cr.Sched, +c: Nat, +x: Nat, +h: {Nat.is_le(x, c) == True{} : Bool}) -> pc.Below(x, Cr.adv(s, c)):
  match s:
    case Cr.Once{d}:
      Unit{}
    case Cr.Every{q}:
      pc.lt_add(x, c, q, h)

def pc.top_pair(+s: Cr.Sched, +c: Nat, +x: Nat, +a: {Nat.is_le(x, c) == True{} : Bool}) -> ({Nat.is_le(x, c) == True{} : Bool} & pc.Below(x, Cr.adv(s, c))):
  (a, pc.below_adv(s, c, x, a))

def pc.top_adv(+ss: List<&2, Nat>, +s: Cr.Sched, +c: Nat, -nx: Maybe<&2, Nat>, t: pc.Top(ss, c, nx)) -> pc.Top(ss, c, Cr.adv(s, c)):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> +u:
      (a, b) = t
      pc.top_pair(s, c, x, a)

def pc.once_adv(+s: Cr.Sched, +ss: List<&2, Nat>, +c: Nat, -nx: Maybe<&2, Nat>, o: pc.OnceG(s, ss, nx)) -> pc.OnceG(s, ss, Cr.adv(s, c)):
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          Unit{}
        case +x <> +t:
          (a, b) = o
          (a, {==})
    case Cr.Every{q}:
      Unit{}

def pc.ends_active(+s: Cr.Sched, -rs: List<&2, Nat>) -> Cr.EndsOf(s, Cr.Active{}, rs):
  match s:
    case Cr.Once{d}:
      Unit{}
    case Cr.Every{q}:
      Unit{}

# the new occurrence n lies after every one that started
def pc.desc_push(+ss: List<&2, Nat>, +n: Nat, -c: Nat, d: Cr.Desc(ss), t: pc.Top(ss, c, Some{n})) -> Cr.DescFrom(n, ss):
  match ss:
    case Nil{}:
      Unit{}
    case +y <> +u:
      (a, b) = t
      (b, d)

def pc.once_new(+s: Cr.Sched, +ss: List<&2, Nat>, +n: Nat, +c: Nat, o: pc.OnceG(s, ss, Some{n})) -> pc.OnceG(s, n <> ss, Cr.adv(s, c)):
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          ({==}, {==})
        case +x <> +t:
          (a, b) = o
          pc.some_none(({x <> t == Nil{} : List<&2, Nat>} & {None{} == None{} : Maybe<&2, Nat>}), n, b)
    case Cr.Every{q}:
      Unit{}

# a due job with no claim: the claim, the run and the start are p's
def pc.take_new(+p: Nat, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +le: {Nat.is_le(n, c) == True{} : Bool}, +al: {Cr.has(p, dead) == False{} : Bool}, g: pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, Some{n}, k, None{}, rs, ss, h})) -> pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, Cr.adv(s, c), k, Some{Cr.Claim{n, p}}, p <> rs, n <> ss, h}):
  match rs:
    case Nil{}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, h7) = g6
      ({==}, ((al, Unit{}), (pc.desc_push(ss, n, c, h3, h4), (pc.top_pair(s, c, n, le), (pc.once_new(s, ss, n, c, h5), (h6, pc.ends_active(s, [p])))))))
    case +o <> +t:
      match t:
        case Nil{}:
          (h1, g2) = g
          match h1:
        case +x <> +u:
          (h1, g2) = g
          match h1:

# a due job with a claim only rolls its next run
def pc.take_skip(+c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, +x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, g: pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, Some{n}, k, Some{x}, rs, ss, h})) -> pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, Cr.adv(s, c), k, Some{x}, rs, ss, h}):
  (h1, g2) = g
  (h2, g3) = g2
  (h3, g4) = g3
  (h4, g5) = g4
  (h5, g6) = g5
  (h6, h7) = g6
  (h1, (h2, (h3, (pc.top_adv(ss, s, c, Some{n}, h4), (pc.once_adv(s, ss, c, Some{n}, h5), (h6, h7))))))

def pc.take_due(b: Bool, +p: Nat, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +eq: {Nat.is_le(n, c) == b : Bool}, +al: {Cr.has(p, dead) == False{} : Bool}, g: pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, Some{n}, k, cl, rs, ss, h})) -> pc.G(c, dead, Cr.take.due(b, p, c, i, s, n, k, cl, rs, ss, h)):
  match b:
    case False{}:
      g
    case True{}:
      match cl:
        case None{}:
          pc.take_new(p, c, dead, i, s, n, k, rs, ss, h, eq, al, g)
        case Some{+x}:
          pc.take_skip(c, dead, i, s, n, k, x, rs, ss, h, g)

def pc.take_nx(+nx: Maybe<&2, Nat>, +p: Nat, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +al: {Cr.has(p, dead) == False{} : Bool}, g: pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, nx, k, cl, rs, ss, h})) -> pc.G(c, dead, Cr.take.next(p, c, i, s, nx, k, cl, rs, ss, h)):
  match nx:
    case None{}:
      g
    case Some{+n}:
      pc.take_due(Nat.is_le(n, c), p, c, dead, i, s, n, k, cl, rs, ss, h, {==}, al, g)

def pc.g_take(+p: Nat, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +al: {Cr.has(p, dead) == False{} : Bool}, g: pc.G(c, dead, j)) -> pc.G(c, dead, Cr.take(p, c, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match st:
        case Cr.Active{}:
          pc.take_nx(nx, p, c, dead, i, s, k, cl, rs, ss, h, al, g)
        case Cr.Paused{}:
          g
        case Cr.Finished{}:
          g
        case Cr.Cancelled{}:
          g

def cron.pc.void(-A: Type, e: Empty) -> A:
  match e:

def cron.pc.or_false_r(a: Bool, h: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

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

# Shapes the invariant keeps
# --------------------------

def pc.top_none(+ss: List<&2, Nat>, +c: Nat, -nx: Maybe<&2, Nat>, t: pc.Top(ss, c, nx)) -> pc.Top(ss, c, None{}):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> +u:
      (a, b) = t
      (a, Unit{})

def pc.once_none(+s: Cr.Sched, +ss: List<&2, Nat>, -nx: Maybe<&2, Nat>, o: pc.OnceG(s, ss, nx)) -> pc.OnceG(s, ss, None{}):
  match s:
    case Cr.Once{d}:
      match ss:
        case Nil{}:
          Unit{}
        case +x <> +t:
          (a, b) = o
          (a, {==})
    case Cr.Every{q}:
      Unit{}

def pc.ends_nil(+s: Cr.Sched, +st: Cr.Status) -> Cr.EndsOf(s, st, Nil{}):
  match s:
    case Cr.Once{d}:
      match st:
        case Cr.Finished{}:
          {==}
        case Cr.Active{}:
          Unit{}
        case Cr.Paused{}:
          Unit{}
        case Cr.Cancelled{}:
          Unit{}
    case Cr.Every{q}:
      Unit{}

def pc.ends_cancel(+s: Cr.Sched, -rs: List<&2, Nat>) -> Cr.EndsOf(s, Cr.Cancelled{}, rs):
  match s:
    case Cr.Once{d}:
      Unit{}
    case Cr.Every{q}:
      Unit{}

# an active job's count holds for any status
def pc.cnt_down(+st: Cr.Status, +k: Nat, +h: List<&2, Cr.Mark>, c6: pc.Cnt(Cr.Active{}, k, h)) -> pc.Cnt(st, k, h):
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

# A recovery keeps the invariant
# ------------------------------

def pc.no_clear(b: Bool, +hd: Bool, live: {hd == False{} : Bool}) -> {Bool.or(Bool.and(b, Bool.not(Bool.or(b, False{}))), hd) == False{} : Bool}:
  match b:
    case True{}:
      live
    case False{}:
      live

def pc.clears_at(+p: Nat, +o: Nat, +w: Nat, +dead: List<&2, Nat>, ow: {o == w : Nat}, nc: {Cr.clears(p, w, [w], dead) == False{} : Bool}) -> {Cr.clears(p, o, [w], dead) == False{} : Bool}:
  %Equal.sym(Nat, o, w, ow) : {Cr.clears(p, _, [w], dead) == False{} : Bool}
  nc

# a claim a recovery clears has no run: the run of an alive process
# holds it, and only its owner runs it
def pc.rec_none(+p: Nat, +o: Nat, +w: Nat, +dead: List<&2, Nat>, ow: {o == w : Nat}, live: {Cr.has(w, dead) == False{} : Bool}, eq: {Cr.clears(p, o, [w], dead) == True{} : Bool}) -> Empty:
  +no = pc.clears_at(p, o, w, dead, ow, pc.no_clear(Nat.is_eq(w, p), Cr.has(w, dead), live))
  cron.pc.absurd(Empty, Equal.trans(Bool, True{}, Cr.clears(p, o, [w], dead), False{}, Equal.sym(Bool, Cr.clears(p, o, [w], dead), True{}, eq), no))

def pc.rec_end(+s: Cr.Sched, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +x: Cr.Claim, g: pc.G(c, dead, Cr.Job{i, s, Cr.Active{}, nx, k, Some{x}, Nil{}, ss, h})) -> pc.G(c, dead, Cr.recover.end(Cr.is_once(s), i, s, nx, k, Nil{}, ss, h)):
  match s:
    case Cr.Once{+d}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, h7) = g6
      (Unit{}, (Unit{}, (h3, (pc.top_none(ss, c, nx, h4), (pc.once_none(Cr.Once{d}, ss, nx, h5), (pc.cnt_down(Cr.Finished{}, k, h, h6), {==}))))))
    case Cr.Every{q}:
      g

def pc.rec_go(b: Bool, +rs: List<&2, Nat>, +st: Cr.Status, +p: Nat, +o: Nat, +xo: Nat, +dead: List<&2, Nat>, +c: Nat, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, eq: {Cr.clears(p, o, rs, dead) == b : Bool}, g: pc.G(c, dead, Cr.Job{i, s, st, nx, k, Some{Cr.Claim{xo, o}}, rs, ss, h})) -> pc.G(c, dead, Cr.recover.go(b, i, s, st, nx, k, Cr.Claim{xo, o}, rs, ss, h)):
  match b:
    case False{}:
      g
    case True{}:
      match rs:
        case Nil{}:
          match st:
            case Cr.Active{}:
              pc.rec_end(s, c, dead, i, nx, k, ss, h, Cr.Claim{xo, o}, g)
            case Cr.Paused{}:
              g
            case Cr.Finished{}:
              g
            case Cr.Cancelled{}:
              g
        case +w <> +t:
          match t:
            case Nil{}:
              (h1, g2) = g
              (h2, g3) = g2
              (live, u) = h2
              cron.pc.void(pc.G(c, dead, Cr.recover.go(True{}, i, s, st, nx, k, Cr.Claim{xo, o}, [w], ss, h)), pc.rec_none(p, o, w, dead, h1, live, eq))
            case +y <> +v:
              (h1, g2) = g
              match h1:

def pc.g_recover(+p: Nat, +dead: List<&2, Nat>, +c: Nat, +j: Cr.Job, g: pc.G(c, dead, j)) -> pc.G(c, dead, Cr.recover(p, dead, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          g
        case Some{+x}:
          match x:
            case Cr.Claim{+xo, +o}:
              pc.rec_go(Cr.clears(p, o, rs, dead), rs, st, p, o, xo, dead, c, i, s, nx, k, ss, h, {==}, g)

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

def pc.top_fail(+ss: List<&2, Nat>, +c: Nat, +nx: Maybe<&2, Nat>, +k: Nat, t: pc.Top(ss, c, nx)) -> pc.Top(ss, c, Some{Cr.later(nx, Nat.add(c, Cr.delay(k)))}):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> +u:
      (a, b) = t
      pc.top_fail2(x, c, nx, k, a, b)

def pc.fin_fail(b: Bool, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +q: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +eqb: {Nat.is_lt(1n+k, Cr.CAP()) == b : Bool}, h3: Cr.Desc(ss), h4: pc.Top(ss, c, nx), +ek: {k == Cr.trail(h) : Nat}, +lt: {Nat.is_lt(k, Cr.CAP()) == True{} : Bool}) -> pc.G(c, dead, Cr.finish.fail(b, c, i, Cr.Every{q}, nx, 1n+k, Nil{}, ss, Cr.MLoss{} <> h)):
  match b:
    case True{}:
      (Unit{}, (Unit{}, (h3, (pc.top_fail(ss, c, nx, 1n+k, h4), (Unit{}, ((Equal.cong(Nat, Nat, v => 1n+v, k, Cr.trail(h), ek), eqb), Unit{}))))))
    case False{}:
      (Unit{}, (Unit{}, (h3, (pc.top_none(ss, c, nx, h4), (Unit{}, ((Equal.cong(Nat, Nat, v => 1n+v, k, Cr.trail(h), ek), pc.lt_succ_le(k, Cr.CAP(), lt)), Unit{}))))))

def pc.cnt_fin(+o: Cr.Out, +k: Nat, +h: List<&2, Cr.Mark>, c6: pc.Cnt(Cr.Active{}, k, h)) -> pc.Cnt(Cr.Finished{}, Cr.count.streak(o, k), Cr.count.hist(o, h)):
  match o:
    case Cr.Win{}:
      ({==}, {==})
    case Cr.Loss{}:
      (ek, lt) = c6
      (Equal.cong(Nat, Nat, v => 1n+v, k, Cr.trail(h), ek), pc.lt_succ_le(k, Cr.CAP(), lt))
    case Cr.Skip{}:
      (ek, lt) = c6
      (ek, pc.lt_le(k, Cr.CAP(), lt))

def pc.fin_count(+s: Cr.Sched, +o: Cr.Out, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, h3: Cr.Desc(ss), h4: pc.Top(ss, c, nx), h5: pc.OnceG(s, ss, nx), h6: pc.Cnt(Cr.Active{}, k, h)) -> pc.G(c, dead, Cr.finish.count(Cr.is_once(s), c, o, i, s, nx, k, Nil{}, ss, h)):
  match s:
    case Cr.Once{+d}:
      (Unit{}, (Unit{}, (h3, (pc.top_none(ss, c, nx, h4), (pc.once_none(Cr.Once{d}, ss, nx, h5), (pc.cnt_fin(o, k, h, h6), {==}))))))
    case Cr.Every{+q}:
      match o:
        case Cr.Win{}:
          (Unit{}, (Unit{}, (h3, (h4, (Unit{}, (({==}, {==}), Unit{}))))))
        case Cr.Skip{}:
          (Unit{}, (Unit{}, (h3, (pc.top_adv(ss, Cr.Every{q}, c, nx, h4), (Unit{}, (h6, Unit{}))))))
        case Cr.Loss{}:
          (ek, lt) = h6
          pc.fin_fail(Nat.is_lt(1n+k, Cr.CAP()), c, dead, i, q, nx, k, ss, h, {==}, h3, h4, ek, lt)

def pc.fin_st(+st: Cr.Status, +x: Cr.Claim, +c: Nat, +dead: List<&2, Nat>, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, h3: Cr.Desc(ss), h4: pc.Top(ss, c, nx), h5: pc.OnceG(s, ss, nx), h6: pc.Cnt(st, k, h)) -> pc.G(c, dead, Cr.finish.own(True{}, x, c, o, i, s, st, nx, k, Nil{}, ss, h)):
  match st:
    case Cr.Active{}:
      pc.fin_count(s, o, c, dead, i, nx, k, ss, h, h3, h4, h5, h6)
    case Cr.Paused{}:
      (Unit{}, (Unit{}, (h3, (h4, (h5, (h6, pc.ends_nil(s, Cr.Paused{})))))))
    case Cr.Finished{}:
      (Unit{}, (Unit{}, (h3, (h4, (h5, (h6, pc.ends_nil(s, Cr.Finished{})))))))
    case Cr.Cancelled{}:
      (Unit{}, (Unit{}, (h3, (h4, (h5, (h6, pc.ends_nil(s, Cr.Cancelled{})))))))

# the run of p is its claim's: releasing it leaves no run
def pc.fin_run(b: Bool, +rs: List<&2, Nat>, +cl: Maybe<&2, Cr.Claim>, +p: Nat, +c: Nat, +o: Cr.Out, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, eq: {Cr.has(p, rs) == b : Bool}, g: pc.G(c, dead, Cr.Job{i, s, st, nx, k, cl, rs, ss, h})) -> pc.G(c, dead, Cr.finish.run(b, p, c, o, i, s, st, nx, k, cl, rs, ss, h)):
  match b:
    case False{}:
      g
    case True{}:
      match rs:
        case Nil{}:
          cron.pc.absurdF(pc.G(c, dead, Cr.finish.run(True{}, p, c, o, i, s, st, nx, k, cl, Nil{}, ss, h)), eq)
        case +w <> +t:
          match t:
            case +y <> +u:
              (h1, g2) = g
              match h1:
            case Nil{}:
              match cl:
                case None{}:
                  (h1, g2) = g
                  match h1:
                case Some{+x}:
                  match x:
                    case Cr.Claim{+xo, +w2}:
                      (h1, g2) = g
                      (h2, g3) = g2
                      (h3, g4) = g3
                      (h4, g5) = g4
                      (h5, g6) = g5
                      (h6, h7) = g6
                      +ewp = cron.pc.eq_of(w, p, cron.pc.or_false_r(Nat.is_eq(w, p), eq))
                      +w2p = Equal.trans(Nat, w2, w, p, h1, ewp)
                      %Equal.sym(Nat, w2, p, w2p) : pc.G(c, dead, Cr.finish.own(Nat.is_eq(_, p), Cr.Claim{xo, _}, c, o, i, s, st, nx, k, Cr.drop(p, [w]), ss, h))
                      %Equal.sym(Nat, w, p, ewp) : pc.G(c, dead, Cr.finish.own(Nat.is_eq(p, p), Cr.Claim{xo, p}, c, o, i, s, st, nx, k, Cr.drop.put(Nat.is_eq(_, p), _, Nil{}), ss, h))
                      %Equal.sym(Bool, Nat.is_eq(p, p), True{}, cron.pc.eq_refl(p)) : pc.G(c, dead, Cr.finish.own(_, Cr.Claim{xo, p}, c, o, i, s, st, nx, k, Cr.drop.put(_, p, Nil{}), ss, h))
                      pc.fin_st(st, Cr.Claim{xo, p}, c, dead, o, i, s, nx, k, ss, h, h3, h4, h5, h6)

def pc.g_finish(+p: Nat, +c: Nat, +o: Cr.Out, +dead: List<&2, Nat>, +j: Cr.Job, g: pc.G(c, dead, j)) -> pc.G(c, dead, Cr.finish(p, c, o, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      pc.fin_run(Cr.has(p, rs), rs, cl, p, c, o, dead, i, s, st, nx, k, ss, h, {==}, g)

def pc.pick_fin(b: Bool, +p: Nat, +c: Nat, +o: Cr.Out, +dead: List<&2, Nat>, +j: Cr.Job, g: pc.G(c, dead, j)) -> pc.G(c, dead, Cr.job.pick(b, Cr.finish(p, c, o, j), j)):
  match b:
    case True{}:
      pc.g_finish(p, c, o, dead, j, g)
    case False{}:
      g

# User actions keep the invariant
# -------------------------------

def pc.g_cancel(+c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: pc.G(c, dead, j)) -> pc.G(c, dead, Cr.cancel(j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match st:
        case Cr.Cancelled{}:
          g
        case Cr.Active{}:
          (h1, g2) = g
          (h2, g3) = g2
          (h3, g4) = g3
          (h4, g5) = g4
          (h5, g6) = g5
          (h6, h7) = g6
          (h1, (h2, (h3, (pc.top_none(ss, c, nx, h4), (pc.once_none(s, ss, nx, h5), (pc.cnt_down(Cr.Cancelled{}, k, h, h6), pc.ends_cancel(s, rs)))))))
        case Cr.Paused{}:
          (h1, g2) = g
          (h2, g3) = g2
          (h3, g4) = g3
          (h4, g5) = g4
          (h5, g6) = g5
          (h6, h7) = g6
          (h1, (h2, (h3, (pc.top_none(ss, c, nx, h4), (pc.once_none(s, ss, nx, h5), (h6, pc.ends_cancel(s, rs)))))))
        case Cr.Finished{}:
          (h1, g2) = g
          (h2, g3) = g2
          (h3, g4) = g3
          (h4, g5) = g4
          (h5, g6) = g5
          (h6, h7) = g6
          (h1, (h2, (h3, (pc.top_none(ss, c, nx, h4), (pc.once_none(s, ss, nx, h5), (h6, pc.ends_cancel(s, rs)))))))

def pc.pick_cancel(b: Bool, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: pc.G(c, dead, j)) -> pc.G(c, dead, Cr.job.pick(b, Cr.cancel(j), j)):
  match b:
    case True{}:
      pc.g_cancel(c, dead, j, g)
    case False{}:
      g

def pc.g_resume(+c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: pc.G(c, dead, j)) -> pc.G(c, dead, Cr.resume(c, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match s:
        case Cr.Once{+d}:
          g
        case Cr.Every{+q}:
          match st:
            case Cr.Active{}:
              (h1, g2) = g
              (h2, g3) = g2
              (h3, g4) = g3
              (h4, g5) = g4
              (h1, (h2, (h3, (pc.top_adv(ss, Cr.Every{q}, c, nx, h4), (Unit{}, (({==}, {==}), Unit{}))))))
            case Cr.Paused{}:
              (h1, g2) = g
              (h2, g3) = g2
              (h3, g4) = g3
              (h4, g5) = g4
              (h1, (h2, (h3, (pc.top_adv(ss, Cr.Every{q}, c, nx, h4), (Unit{}, (({==}, {==}), Unit{}))))))
            case Cr.Finished{}:
              g
            case Cr.Cancelled{}:
              g

def pc.pick_resume(b: Bool, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: pc.G(c, dead, j)) -> pc.G(c, dead, Cr.job.pick(b, Cr.resume(c, j), j)):
  match b:
    case True{}:
      pc.g_resume(c, dead, j, g)
    case False{}:
      g

# A pass that unwinds, or a process that dies, keeps the invariant
# ----------------------------------------------------------------

def pc.or_ff(a: Bool, +b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      cron.pc.absurd({Bool.or(True{}, b) == False{} : Bool}, ha)
    case False{}:
      hb

def pc.abort_one(b: Bool, +w: Nat, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, g: pc.G(c, dead, Cr.Job{i, s, st, nx, k, cl, [w], ss, h})) -> pc.G(c, dead, Cr.Job{i, s, st, nx, k, cl, Cr.drop.put(b, w, Nil{}), ss, h}):
  match b:
    case True{}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, h7) = g6
      (Unit{}, (Unit{}, (h3, (h4, (h5, (h6, pc.ends_nil(s, st)))))))
    case False{}:
      g

def pc.g_abort(+p: Nat, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: pc.G(c, dead, j)) -> pc.G(c, dead, Cr.unrun(p, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match rs:
        case Nil{}:
          g
        case +w <> +t:
          match t:
            case Nil{}:
              pc.abort_one(Nat.is_eq(w, p), w, c, dead, i, s, st, nx, k, cl, ss, h, g)
            case +y <> +u:
              (h1, g2) = g
              match h1:

def pc.die_one(b: Bool, +w: Nat, +p: Nat, +c: Nat, +dead: List<&2, Nat>, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, eqb: {Nat.is_eq(w, p) == b : Bool}, g: pc.G(c, dead, Cr.Job{i, s, st, nx, k, cl, [w], ss, h})) -> pc.G(c, p <> dead, Cr.Job{i, s, st, nx, k, cl, Cr.drop.put(b, w, Nil{}), ss, h}):
  match b:
    case True{}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h5, g6) = g5
      (h6, h7) = g6
      (Unit{}, (Unit{}, (h3, (h4, (h5, (h6, pc.ends_nil(s, st)))))))
    case False{}:
      (h1, g2) = g
      (h2, g3) = g2
      (live, un) = h2
      (h1, ((pc.or_ff(Nat.is_eq(p, w), Cr.has(w, dead), pc.eq_flip(w, p, eqb), live), Unit{}), g3))

def pc.g_die(+p: Nat, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: pc.G(c, dead, j)) -> pc.G(c, p <> dead, Cr.unrun(p, j)):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      match rs:
        case Nil{}:
          (h1, g2) = g
          (h2, g3) = g2
          (Unit{}, (Unit{}, g3))
        case +w <> +t:
          match t:
            case Nil{}:
              pc.die_one(Nat.is_eq(w, p), w, p, c, dead, i, s, st, nx, k, cl, ss, h, {==}, g)
            case +y <> +u:
              (h1, g2) = g
              match h1:

# Every event keeps the invariant
# -------------------------------

# what an event needs of its process: a claim, that it is alive
def pc.Alive(e: Cr.Ev, +dead: List<&2, Nat>) -> Data:
  match e:
    case Cr.Take{p}:
      {Cr.has(p, dead) == False{} : Bool}
    case Cr.Create{p, s}:
      Unit
    case Cr.Recover{p}:
      Unit
    case Cr.Finish{p, i, o}:
      Unit
    case Cr.Abort{p}:
      Unit
    case Cr.Die{p}:
      Unit
    case Cr.Cancel{p, i}:
      Unit
    case Cr.Resume{p, i}:
      Unit
    case Cr.Tick{d}:
      Unit
    case Cr.RawJob{t}:
      Unit
    case Cr.RawClaim{t}:
      Unit
    case Cr.Corrupt{t}:
      Unit

def pc.dead_after(e: Cr.Ev, +dead: List<&2, Nat>) -> List<&2, Nat>:
  match e:
    case Cr.Die{p}:
      p <> dead
    case Cr.Take{p}:
      dead
    case Cr.Create{p, s}:
      dead
    case Cr.Recover{p}:
      dead
    case Cr.Finish{p, i, o}:
      dead
    case Cr.Abort{p}:
      dead
    case Cr.Cancel{p, i}:
      dead
    case Cr.Resume{p, i}:
      dead
    case Cr.Tick{d}:
      dead
    case Cr.RawJob{t}:
      dead
    case Cr.RawClaim{t}:
      dead
    case Cr.Corrupt{t}:
      dead

def pc.g_job(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +al: pc.Alive(e, dead), g: pc.G(c, dead, j)) -> pc.G(c, pc.dead_after(e, dead), Cr.job(e, c, dead, j)):
  match e:
    case Cr.Take{+p}:
      pc.g_take(p, c, dead, j, al, g)
    case Cr.Recover{+p}:
      pc.g_recover(p, dead, c, j, g)
    case Cr.Finish{+p, +i, +o}:
      pc.pick_fin(Nat.is_eq(Cr.Job.id(j), i), p, c, o, dead, j, g)
    case Cr.Abort{+p}:
      pc.g_abort(p, c, dead, j, g)
    case Cr.Die{+p}:
      pc.g_die(p, c, dead, j, g)
    case Cr.Cancel{+p, +i}:
      pc.pick_cancel(Nat.is_eq(Cr.Job.id(j), i), c, dead, j, g)
    case Cr.Resume{+p, +i}:
      pc.pick_resume(Nat.is_eq(Cr.Job.id(j), i), c, dead, j, g)
    case Cr.Create{p, s}:
      g
    case Cr.Tick{d}:
      g
    case Cr.RawJob{t}:
      g
    case Cr.RawClaim{t}:
      g
    case Cr.Corrupt{t}:
      g

def pc.all_recs(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +al: pc.Alive(e, dead), g: pc.AllG(c, dead, rs)) -> pc.AllG(c, pc.dead_after(e, dead), Cr.recs(e, c, dead, rs)):
  match rs:
    case Nil{}:
      Unit{}
    case r <> t:
      match r:
        case Cr.Known{+j}:
          (a, b) = g
          (pc.g_job(e, c, dead, j, al, a), pc.all_recs(e, c, dead, t, al, b))
        case Cr.Raw{x}:
          pc.all_recs(e, c, dead, t, al, g)

def pc.all_append(+c: Nat, +dead: List<&2, Nat>, xs: List<&2, Cr.Rec>, +ys: List<&2, Cr.Rec>, gx: pc.AllG(c, dead, xs), gy: pc.AllG(c, dead, ys)) -> pc.AllG(c, dead, List.append(&2, Cr.Rec, xs, ys)):
  match xs:
    case Nil{}:
      gy
    case r <> t:
      match r:
        case Cr.Known{+j}:
          (a, b) = gx
          (a, pc.all_append(c, dead, t, ys, b, gy))
        case Cr.Raw{x}:
          pc.all_append(c, dead, t, ys, gx, gy)

def pc.top_tick(+ss: List<&2, Nat>, +c: Nat, +d: Nat, -nx: Maybe<&2, Nat>, t: pc.Top(ss, c, nx)) -> pc.Top(ss, Nat.add(c, d), nx):
  match ss:
    case Nil{}:
      Unit{}
    case +x <> +u:
      (a, b) = t
      (cron.pc.le_add(x, c, d, a), b)

def pc.g_tick(+c: Nat, +d: Nat, +dead: List<&2, Nat>, +j: Cr.Job, g: pc.G(c, dead, j)) -> pc.G(Nat.add(c, d), dead, j):
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      (h1, g2) = g
      (h2, g3) = g2
      (h3, g4) = g3
      (h4, g5) = g4
      (h1, (h2, (h3, (pc.top_tick(ss, c, d, nx, h4), g5))))

def pc.all_tick(+c: Nat, +d: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, g: pc.AllG(c, dead, rs)) -> pc.AllG(Nat.add(c, d), dead, rs):
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

def pc.once_empty(+s: Cr.Sched, -nx: Maybe<&2, Nat>) -> pc.OnceG(s, Nil{}, nx):
  match s:
    case Cr.Once{d}:
      Unit{}
    case Cr.Every{q}:
      Unit{}

def pc.g_new(+c: Nat, +dead: List<&2, Nat>, +n: Nat, +sc: Cr.Sched) -> pc.G(c, dead, Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}):
  (Unit{}, (Unit{}, (Unit{}, (Unit{}, (pc.once_empty(sc, Some{Cr.first(sc, c)}), (({==}, {==}), pc.ends_active(sc, Nil{})))))))

def pc.alive_create(b: Bool, +c: Nat, +dead: List<&2, Nat>, +n: Nat, +sc: Cr.Sched, +rs: List<&2, Cr.Rec>, -bad: Maybe<&2, Nat>, -rd: List<&2, Nat>, -aside: List<&2, Nat>, inv: pc.AllG(c, dead, rs)) -> pc.Inv(Cr.step.alive(b, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]), rd, dead, c, 1n+n, Cr.heal(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match b:
    case False{}:
      pc.all_append(c, dead, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}], inv, (pc.g_new(c, dead, n, sc), Unit{}))
    case True{}:
      inv

def pc.alive_take(b: Bool, +p: Nat, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, -b1: Maybe<&2, Nat>, -rd1: List<&2, Nat>, -n1: Nat, -a1: List<&2, Nat>, -b0: Maybe<&2, Nat>, -rd0: List<&2, Nat>, -n0: Nat, -a0: List<&2, Nat>, eqb: {Cr.has(p, dead) == b : Bool}, inv: pc.AllG(c, dead, rs)) -> pc.Inv(Cr.step.alive(b, Cr.S{b1, Cr.recs(Cr.Take{p}, c, dead, rs), rd1, dead, c, n1, a1}, Cr.S{b0, rs, rd0, dead, c, n0, a0})):
  match b:
    case False{}:
      pc.all_recs(Cr.Take{p}, c, dead, rs, eqb, inv)
    case True{}:
      inv

def pc.alive_recs(b: Bool, +e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, -b1: Maybe<&2, Nat>, -rd1: List<&2, Nat>, -n1: Nat, -a1: List<&2, Nat>, -b0: Maybe<&2, Nat>, -rd0: List<&2, Nat>, -n0: Nat, -a0: List<&2, Nat>, +al: pc.Alive(e, dead), de: {pc.dead_after(e, dead) == dead : List<&2, Nat>}, inv: pc.AllG(c, dead, rs)) -> pc.Inv(Cr.step.alive(b, Cr.S{b1, Cr.recs(e, c, dead, rs), rd1, dead, c, n1, a1}, Cr.S{b0, rs, rd0, dead, c, n0, a0})):
  match b:
    case False{}:
      %de : pc.AllG(c, _, Cr.recs(e, c, dead, rs))
      pc.all_recs(e, c, dead, rs, al, inv)
    case True{}:
      inv

def pc.raw_job(bad: Maybe<&2, Nat>, +t: Nat, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, -rd: List<&2, Nat>, -n: Nat, -aside: List<&2, Nat>, inv: pc.AllG(c, dead, rs)) -> pc.Inv(Cr.step.raw(bad, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Raw{t}]), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match bad:
    case None{}:
      pc.all_append(c, dead, rs, [Cr.Raw{t}], inv, Unit{})
    case Some{x}:
      inv

def pc.raw_claim(bad: Maybe<&2, Nat>, +t: Nat, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, -rd: List<&2, Nat>, -n: Nat, -aside: List<&2, Nat>, inv: pc.AllG(c, dead, rs)) -> pc.Inv(Cr.step.raw(bad, Cr.S{None{}, rs, List.append(&2, Nat, rd, [t]), dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})):
  match bad:
    case None{}:
      inv
    case Some{x}:
      inv

def pc.inv_step(s: Cr.S, +e: Cr.Ev, inv: pc.Inv(s)) -> pc.Inv(Cr.step(s, e)):
  match s:
    case Cr.S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      match e:
        case Cr.Create{+p, +sc}:
          pc.alive_create(Cr.has(p, dead), c, dead, n, sc, rs, bad, rd, aside, inv)
        case Cr.Take{+p}:
          pc.alive_take(Cr.has(p, dead), p, c, dead, rs, None{}, rd, n, Cr.heal(bad, aside), bad, rd, n, aside, {==}, inv)
        case Cr.Recover{+p}:
          pc.alive_recs(Cr.has(p, dead), Cr.Recover{p}, c, dead, rs, None{}, rd, n, Cr.heal(bad, aside), bad, rd, n, aside, Unit{}, {==}, inv)
        case Cr.Finish{+p, +i, +o}:
          pc.alive_recs(Cr.has(p, dead), Cr.Finish{p, i, o}, c, dead, rs, None{}, rd, n, Cr.heal(bad, aside), bad, rd, n, aside, Unit{}, {==}, inv)
        case Cr.Abort{+p}:
          pc.alive_recs(Cr.has(p, dead), Cr.Abort{p}, c, dead, rs, bad, rd, n, aside, bad, rd, n, aside, Unit{}, {==}, inv)
        case Cr.Die{+p}:
          pc.all_recs(Cr.Die{p}, c, dead, rs, Unit{}, inv)
        case Cr.Cancel{+p, +i}:
          pc.alive_recs(Cr.has(p, dead), Cr.Cancel{p, i}, c, dead, rs, bad, rd, n, aside, bad, rd, n, aside, Unit{}, {==}, inv)
        case Cr.Resume{+p, +i}:
          pc.alive_recs(Cr.has(p, dead), Cr.Resume{p, i}, c, dead, rs, bad, rd, n, aside, bad, rd, n, aside, Unit{}, {==}, inv)
        case Cr.Tick{+d}:
          pc.all_tick(c, d, dead, rs, inv)
        case Cr.RawJob{+t}:
          pc.raw_job(bad, t, c, dead, rs, rd, n, aside, inv)
        case Cr.RawClaim{+t}:
          pc.raw_claim(bad, t, c, dead, rs, rd, n, aside, inv)
        case Cr.Corrupt{t}:
          Unit{}

def pc.inv_go(evs: List<&2, Cr.Ev>, +s: Cr.S, inv: pc.Inv(s)) -> pc.Inv(Cr.go(evs, s)):
  match evs:
    case Nil{}:
      inv
    case +e <> rest:
      pc.inv_go(rest, Cr.step(s, e), pc.inv_step(s, e, inv))

def pc.inv_run(evs: List<&2, Cr.Ev>) -> pc.Inv(Cr.run(evs)):
  pc.inv_go(evs, Cr.S.empty(), Unit{})

# ---- cron_step ----

# proof_cron_step: the cron laws of LAWS.bend section cron (D2) about one step from
# any state (bend/cron.bend): no step but the file's corruption drops a
# record (`cron_never_drops`); a step of p removes the claim of o only when
# o is p or dead (`cron_claim_owned`); a paused job stays paused through
# every step that is not a user action, and the failure backoff never
# shrinks (the rest of `cron_backoff_bounded`). The invariant laws are in
# PROOF.bend section cron.

# Logic, from PROOF.bend section cron
# --------------------------------

def cron_step.pc.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  cron.pc.absurd(A, e)

# Ids stay
# --------

def pc.id_take_due(b: Bool, +p: Nat, +c: Nat, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.take.due(b, p, c, i, s, n, k, cl, rs, ss, h)) == i : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          {==}

def pc.id_take(+p: Nat, +c: Nat, j: Cr.Job) -> {Cr.Job.id(Cr.take(p, c, j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{+i, +s, st, nx, +k, cl, +rs, +ss, +h}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              {==}
            case Some{+n}:
              pc.id_take_due(Nat.is_le(n, c), p, c, i, s, n, k, cl, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def pc.id_rec_go(b: Bool, st: Cr.Status, +s: Cr.Sched, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.recover.go(b, i, s, st, nx, k, x, rs, ss, h)) == i : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case Cr.Active{}:
          match s:
            case Cr.Once{d}:
              {==}
            case Cr.Every{q}:
              {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def pc.id_recover(+p: Nat, +dead: List<&2, Nat>, j: Cr.Job) -> {Cr.Job.id(Cr.recover(p, dead, j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{+xo, +o}:
              pc.id_rec_go(Cr.clears(p, o, rs, dead), st, s, i, nx, k, Cr.Claim{xo, o}, rs, ss, h)

def pc.id_fail(b: Bool, +c: Nat, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.finish.fail(b, c, i, s, nx, k, rs, ss, h)) == i : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pc.id_count(b: Bool, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.finish.count(b, c, o, i, s, nx, k, rs, ss, h)) == i : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      match o:
        case Cr.Win{}:
          {==}
        case Cr.Skip{}:
          {==}
        case Cr.Loss{}:
          pc.id_fail(Nat.is_lt(1n+k, Cr.CAP()), c, i, s, nx, 1n+k, rs, ss, Cr.MLoss{} <> h)

def pc.id_own(b: Bool, +x: Cr.Claim, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.finish.own(b, x, c, o, i, s, st, nx, k, rs, ss, h)) == i : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case Cr.Active{}:
          pc.id_count(Cr.is_once(s), c, o, i, s, nx, k, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def pc.id_run(b: Bool, +p: Nat, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cr.Job.id(Cr.finish.run(b, p, c, o, i, s, st, nx, k, cl, rs, ss, h)) == i : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{+xo, +w}:
              pc.id_own(Nat.is_eq(w, p), Cr.Claim{xo, w}, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h)

def pc.id_finish(+p: Nat, +c: Nat, +o: Cr.Out, j: Cr.Job) -> {Cr.Job.id(Cr.finish(p, c, o, j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      pc.id_run(Cr.has(p, rs), p, c, o, i, s, st, nx, k, cl, rs, ss, h)

def pc.id_cancel(j: Cr.Job) -> {Cr.Job.id(Cr.cancel(j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Cancelled{}:
          {==}
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}

def pc.id_resume(+c: Nat, j: Cr.Job) -> {Cr.Job.id(Cr.resume(c, j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Cr.Once{d}:
          {==}
        case Cr.Every{q}:
          match st:
            case Cr.Active{}:
              {==}
            case Cr.Paused{}:
              {==}
            case Cr.Finished{}:
              {==}
            case Cr.Cancelled{}:
              {==}

def pc.id_unrun(+p: Nat, j: Cr.Job) -> {Cr.Job.id(Cr.unrun(p, j)) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      {==}

def pc.id_pick(b: Bool, a: Cr.Job, +j: Cr.Job, ea: {Cr.Job.id(a) == Cr.Job.id(j) : Nat}) -> {Cr.Job.id(Cr.job.pick(b, a, j)) == Cr.Job.id(j) : Nat}:
  match b:
    case True{}:
      ea
    case False{}:
      {==}

def pc.id_job(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job) -> {Cr.Job.id(Cr.job(e, c, dead, j)) == Cr.Job.id(j) : Nat}:
  match e:
    case Cr.Take{+p}:
      pc.id_take(p, c, j)
    case Cr.Recover{+p}:
      pc.id_recover(p, dead, j)
    case Cr.Finish{+p, +i, +o}:
      pc.id_pick(Nat.is_eq(Cr.Job.id(j), i), Cr.finish(p, c, o, j), j, pc.id_finish(p, c, o, j))
    case Cr.Abort{+p}:
      pc.id_unrun(p, j)
    case Cr.Die{+p}:
      pc.id_unrun(p, j)
    case Cr.Cancel{+p, +i}:
      pc.id_pick(Nat.is_eq(Cr.Job.id(j), i), Cr.cancel(j), j, pc.id_cancel(j))
    case Cr.Resume{+p, +i}:
      pc.id_pick(Nat.is_eq(Cr.Job.id(j), i), Cr.resume(c, j), j, pc.id_resume(c, j))
    case Cr.Create{p, s}:
      {==}
    case Cr.Tick{d}:
      {==}
    case Cr.RawJob{t}:
      {==}
    case Cr.RawClaim{t}:
      {==}
    case Cr.Corrupt{t}:
      {==}
