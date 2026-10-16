# proof_child: the H5 laws of LAWS.bend (bend/child.bend, the life of one
# subagent).
#
# - The watch: a quiet poll takes 1 ms or more off the clock (`left`) and
#   a failed one a try (`tries`), so a run of them as long as the clock
#   ends the watch (`stalls_in_time`, `unreachable_in_time`); a clock
#   never grows past its full size (`clock_bounded`); progress sets it
#   back to full (`progress_is_not_a_stall`).
# - The report: an invariant `K` holds after any events: every submission
#   in the parent's inbox but the newest is withdrawn, under an id below
#   it (`Kin`), and the task owes the newest id, or the next one once the
#   newest is withdrawn (`Kowe`). Only the newest may be live, which gives
#   `one_live` and `report_once`; a delivery or withdrawal touches only the
#   newest. From any state that owes the report, a reopen and two task
#   steps (three when an abort mark is pending) leave the report queued
#   under the owed id or placed (`ready`), and a delivery of that id
#   places it (`delivered_once`). A potential (1 plus the withdrawn
#   submissions) bounds the inbox and grows only at a withdrawal
#   (`resubmits_per_abort`).

import Base
import ./child.bend as C

# Logic
# -----

def pc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pc.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pc.BD(_, A, Unit)
  Unit{}

def pc.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pc.absurd({False{} == True{} : Bool}, e)

def pc.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      pc.absurd({b == True{} : Bool}, e)

def pc.and_in(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      pc.absurd({Bool.and(False{}, b) == True{} : Bool}, ea)

# Numbers
# -------

def pc.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pc.eq_refl(p)

def pc.eq_succ(+a: Nat) -> {Nat.is_eq(1n+a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pc.eq_succ(p)

def pc.eq_of(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pc.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      pc.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %pc.eq_of(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def pc.le_zero(+b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def pc.le_refl(+a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pc.le_refl(p)

def pc.le_of_eq(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pc.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_of_eq(p, q, e)

def pc.le_succ(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      pc.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_succ(p, q, e)

def pc.le_pred(+a: Nat, +b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n b:
      pc.le_zero(b)
    case 1n+p 0n:
      pc.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_pred(p, q, e)

def pc.le_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      pc.le_zero(c)
    case 1n+p 0n c:
      pc.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      pc.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pc.le_trans(p, q, r, ab, bc)

def pc.sub_le(+a: Nat, +d: Nat) -> {Nat.is_le(Nat.sub(a, d), a) == True{} : Bool}:
  match a d:
    case 0n d:
      {==}
    case 1n+p 0n:
      pc.le_refl(p)
    case 1n+p 1n+e:
      pc.le_succ(Nat.sub(p, e), p, pc.sub_le(p, e))

def pc.le_add(+c: Nat, +x: Nat) -> {Nat.is_le(x, Nat.add(c, x)) == True{} : Bool}:
  match c:
    case 0n:
      pc.le_refl(x)
    case 1n+p:
      pc.le_succ(x, Nat.add(p, x), pc.le_add(p, x))

def pc.le_add_mono(+a: Nat, +x: Nat, +y: Nat, e: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, x), Nat.add(a, y)) == True{} : Bool}:
  match a:
    case 0n:
      e
    case 1n+p:
      pc.le_add_mono(p, x, y, e)

def pc.add_assoc(+a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pc.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# The watch
# ---------

# an owed report stays owed through any more polls
def pc.owe_stops(hs: List<&2, C.Hush>, +cfg: C.Cfg, +k: C.Report) -> {C.Next.watching(C.hush(hs, cfg, C.Owe{k})) == False{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case h <> t:
      pc.owe_stops(t, cfg, k)

# the token the watch holds is no progress
def pc.moved_self(+tok: Maybe<&2, Nat>) -> {False{} == C.moved(tok, tok) : Bool}:
  match tok:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, pc.eq_refl(x)) : {False{} == Bool.not(_) : Bool}
      {==}

# from the clock spend(r, tok, n), quiet polls hs, at least r of them,
# end the watch: each takes 1 ms or more off the r ms left
def pc.stall(hs: List<&2, C.Hush>, +cfg: C.Cfg, +r: Nat, +tok: Maybe<&2, Nat>, +n: Nat, long: {Nat.is_le(r, List.length(&2, C.Hush, hs)) == True{} : Bool}) -> {C.Next.watching(C.hush(hs, cfg, C.spend(r, tok, n))) == False{} : Bool}:
  match hs:
    case Nil{}:
      match r:
        case 0n:
          {==}
        case 1n+p:
          pc.absurd({C.Next.watching(C.hush(Nil{}, cfg, C.spend(1n+p, tok, n))) == False{} : Bool}, long)
    case h <> +t:
      match h:
        case C.Same{+dt}:
          match r:
            case 0n:
              pc.owe_stops(t, cfg, C.Stalled{})
            case 1n+p:
              %pc.moved_self(tok) : {C.Next.watching(C.hush(t, cfg, C.busy(_, cfg, C.W{tok, 1n+p, n}, tok, 1n+dt))) == False{} : Bool}
              pc.stall(t, cfg, Nat.sub(p, dt), tok, C.Cfg.fails(cfg), pc.le_trans(Nat.sub(p, dt), p, List.length(&2, C.Hush, t), pc.sub_le(p, dt), long))
        case C.Miss{+dt}:
          match r:
            case 0n:
              pc.owe_stops(t, cfg, C.Stalled{})
            case 1n+p:
              match n:
                case 0n:
                  pc.owe_stops(t, cfg, C.Unreachable{})
                case 1n+q:
                  match q:
                    case 0n:
                      pc.owe_stops(t, cfg, C.Unreachable{})
                    case 1n+u:
                      pc.stall(t, cfg, Nat.sub(p, dt), tok, 1n+u, pc.le_trans(Nat.sub(p, dt), p, List.length(&2, C.Hush, t), pc.sub_le(p, dt), long))

# a clock with nothing left ends at the next quiet poll
def pc.spent(h: C.Hush, hs: List<&2, C.Hush>, +cfg: C.Cfg, +tok: Maybe<&2, Nat>, +n: Nat) -> {C.Next.watching(C.hush(h <> hs, cfg, C.Watch{C.W{tok, 0n, n}})) == False{} : Bool}:
  match h:
    case C.Same{+dt}:
      %pc.moved_self(tok) : {C.Next.watching(C.hush(hs, cfg, C.busy(_, cfg, C.W{tok, 0n, n}, tok, 1n+dt))) == False{} : Bool}
      pc.owe_stops(hs, cfg, C.Stalled{})
    case C.Miss{+dt}:
      match n:
        case 0n:
          pc.owe_stops(hs, cfg, C.Unreachable{})
        case 1n+q:
          match q:
            case 0n:
              pc.owe_stops(hs, cfg, C.Unreachable{})
            case 1n+u:
              pc.owe_stops(hs, cfg, C.Stalled{})

def pc.stalls_in_time(+cfg: C.Cfg, +w: C.W, +h: C.Hush, +hs: List<&2, C.Hush>, long: {Nat.is_le(C.W.left(w), List.length(&2, C.Hush, h <> hs)) == True{} : Bool}) -> {C.Next.watching(C.hush(h <> hs, cfg, C.Watch{w})) == False{} : Bool}:
  match w:
    case C.W{+tok, +l, +n}:
      match l:
        case 0n:
          pc.spent(h, hs, cfg, tok, n)
        case 1n+p:
          pc.stall(h <> hs, cfg, 1n+p, tok, n, long)

# from the clock spend(r, tok, 1 + q), failed polls ds, more than q of
# them, end the watch
def pc.miss(ds: List<&2, Nat>, +cfg: C.Cfg, +r: Nat, +tok: Maybe<&2, Nat>, +q: Nat, long: {Nat.is_le(1n+q, List.length(&2, Nat, ds)) == True{} : Bool}) -> {C.Next.watching(C.hush(C.misses(ds), cfg, C.spend(r, tok, 1n+q))) == False{} : Bool}:
  match ds:
    case Nil{}:
      pc.absurd({C.Next.watching(C.hush(Nil{}, cfg, C.spend(r, tok, 1n+q))) == False{} : Bool}, long)
    case +d <> +t:
      match r:
        case 0n:
          pc.owe_stops(C.misses(d <> t), cfg, C.Stalled{})
        case 1n+p:
          match q:
            case 0n:
              pc.owe_stops(C.misses(t), cfg, C.Unreachable{})
            case 1n+u:
              pc.miss(t, cfg, Nat.sub(p, d), tok, u, long)

def pc.unreachable_in_time(+cfg: C.Cfg, +w: C.W, +d: Nat, +ds: List<&2, Nat>, long: {Nat.is_le(C.W.tries(w), List.length(&2, Nat, d <> ds)) == True{} : Bool}) -> {C.Next.watching(C.hush(C.misses(d <> ds), cfg, C.Watch{w})) == False{} : Bool}:
  match w:
    case C.W{+tok, +l, +n}:
      match n:
        case 0n:
          pc.owe_stops(C.misses(ds), cfg, C.Unreachable{})
        case 1n+q:
          match q:
            case 0n:
              pc.owe_stops(C.misses(ds), cfg, C.Unreachable{})
            case 1n+u:
              pc.miss(ds, cfg, Nat.sub(l, 1n+d), tok, u, long)

def pc.spend_within(+cfg: C.Cfg, +r: Nat, +tok: Maybe<&2, Nat>, +n: Nat, er: {Nat.is_le(r, C.Cfg.stall(cfg)) == True{} : Bool}, en: {Nat.is_le(n, C.Cfg.fails(cfg)) == True{} : Bool}) -> {C.within(cfg, C.spend(r, tok, n)) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      pc.and_in(Nat.is_le(1n+p, C.Cfg.stall(cfg)), Nat.is_le(n, C.Cfg.fails(cfg)), er, en)

def pc.busy_within(b: Bool, +cfg: C.Cfg, +w: C.W, +t: Maybe<&2, Nat>, +e: Nat, full: {C.within(cfg, C.Watch{w}) == True{} : Bool}) -> {C.within(cfg, C.busy(b, cfg, w, t, e)) == True{} : Bool}:
  match b:
    case True{}:
      pc.and_in(Nat.is_le(C.Cfg.stall(cfg), C.Cfg.stall(cfg)), Nat.is_le(C.Cfg.fails(cfg), C.Cfg.fails(cfg)), pc.le_refl(C.Cfg.stall(cfg)), pc.le_refl(C.Cfg.fails(cfg)))
    case False{}:
      match w:
        case C.W{+tok, +l, +n}:
          pc.spend_within(cfg, Nat.sub(l, e), tok, C.Cfg.fails(cfg), pc.le_trans(Nat.sub(l, e), l, C.Cfg.stall(cfg), pc.sub_le(l, e), pc.and_l(Nat.is_le(l, C.Cfg.stall(cfg)), Nat.is_le(n, C.Cfg.fails(cfg)), full)), pc.le_refl(C.Cfg.fails(cfg)))

def pc.look_within(o: C.Obs, +cfg: C.Cfg, +w: C.W, +e: Nat, +full: {C.within(cfg, C.Watch{w}) == True{} : Bool}) -> {C.within(cfg, C.look(cfg, w, e, o)) == True{} : Bool}:
  match o:
    case C.Busy{+t}:
      pc.busy_within(C.moved(C.W.tok(w), t), cfg, w, t, e, full)
    case C.Lost{}:
      match w:
        case C.W{+tok, +l, +n}:
          match n:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+u:
                  pc.spend_within(cfg, Nat.sub(l, e), tok, 1n+u, pc.le_trans(Nat.sub(l, e), l, C.Cfg.stall(cfg), pc.sub_le(l, e), pc.and_l(Nat.is_le(l, C.Cfg.stall(cfg)), Nat.is_le(2n+u, C.Cfg.fails(cfg)), full)), pc.le_pred(1n+u, C.Cfg.fails(cfg), pc.and_r(Nat.is_le(l, C.Cfg.stall(cfg)), Nat.is_le(2n+u, C.Cfg.fails(cfg)), full)))
    case C.Answered{r}:
      match r:
        case True{}:
          {==}
        case False{}:
          {==}
    case C.Broke{}:
      {==}
    case C.Gone{}:
      {==}

def pc.clock_bounded(+cfg: C.Cfg, +w: C.W, +e: Nat, o: C.Obs, full: {C.within(cfg, C.Watch{w}) == True{} : Bool}) -> {C.within(cfg, C.look(cfg, w, e, o)) == True{} : Bool}:
  pc.look_within(o, cfg, w, e, full)

def pc.progress_is_not_a_stall(+cfg: C.Cfg, +w: C.W, +e: Nat, +x: Nat, news: {C.moved(C.W.tok(w), Some{x}) == True{} : Bool}) -> {C.look(cfg, w, e, C.Busy{Some{x}}) == C.Watch{C.W.fresh(cfg, Some{x})} : C.Next}:
  %Equal.sym(Bool, C.moved(C.W.tok(w), Some{x}), True{}, news) : {C.busy(_, cfg, w, Some{x}, e) == C.Watch{C.W.fresh(cfg, Some{x})} : C.Next}
  {==}

# The report
# ----------

# a clash of constructors proves anything
def pc.MD(x: Maybe<&2, C.Fate>, t: Type, u: Type) -> Type:
  match x:
    case None{}:
      t
    case Some{f}:
      u

def pc.none_some(-A: Type, -f: C.Fate, e: {None{} == Some{f} : Maybe<&2, C.Fate>}) -> A:
  %e : pc.MD(_, Unit, A)
  Unit{}

def pc.ND(n: Nat, t: Type, u: Type) -> Type:
  match n:
    case 0n:
      t
    case 1n+p:
      u

def pc.zero_succ(-A: Type, -p: Nat, e: {0n == 1n+p : Nat}) -> A:
  %e : pc.ND(_, Unit, A)
  Unit{}

# x is 0 and 1 at once
def pc.one_zero(-A: Type, x: Nat, e: {0n == x : Nat}, r: {Nat.is_eq(x, 1n) == True{} : Bool}) -> A:
  match x:
    case 0n:
      pc.absurd(A, r)
    case 1n+p:
      pc.zero_succ(A, p, e)

# j < n and j = n at once
def pc.lt_ne(-A: Type, +j: Nat, +n: Nat, lt: {Nat.is_le(1n+j, n) == True{} : Bool}, eq: {Nat.is_eq(j, n) == True{} : Bool}) -> A:
  match j n:
    case 0n 0n:
      pc.absurd(A, lt)
    case 0n 1n+q:
      pc.absurd(A, eq)
    case 1n+p 0n:
      pc.absurd(A, eq)
    case 1n+p 1n+q:
      pc.lt_ne(A, p, q, lt, eq)

def pc.eq_next(+m: Nat, +n: Nat, e: {Nat.is_eq(m, n) == True{} : Bool}) -> {Nat.is_eq(m, 1n+n) == False{} : Bool}:
  match m n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pc.absurd({Nat.is_eq(0n, 2n+q) == False{} : Bool}, e)
    case 1n+p 0n:
      pc.absurd({Nat.is_eq(1n+p, 1n) == False{} : Bool}, e)
    case 1n+p 1n+q:
      pc.eq_next(p, q, e)

def pc.isW(f: C.Fate) -> Bool:
  match f:
    case C.Queued{}:
      False{}
    case C.Withdrawn{}:
      True{}
    case C.Placed{}:
      False{}

def pc.empty(inbox: List<&2, C.Sub>) -> Bool:
  match inbox:
    case Nil{}:
      True{}
    case s <> rest:
      False{}

# every submission in rest is withdrawn, under an id below m (newest
# first)
def pc.Old(rest: List<&2, C.Sub>, +m: Nat) -> Bool:
  match rest:
    case Nil{}:
      True{}
    case s <> r:
      match s:
        case C.Sub{+j, f}:
          Bool.and(pc.isW(f), Bool.and(Nat.is_le(1n+j, m), pc.Old(r, j)))

# every submission but the newest is withdrawn
def pc.Kin(inbox: List<&2, C.Sub>) -> Bool:
  match inbox:
    case Nil{}:
      True{}
    case s <> rest:
      match s:
        case C.Sub{+m, f}:
          pc.Old(rest, m)

# owing id n: the newest submission has id n (same), or id n - 1 and is
# withdrawn
def pc.Kowe.at(same: Bool, +n: Nat, +m: Nat, f: C.Fate) -> Bool:
  match same:
    case True{}:
      True{}
    case False{}:
      Bool.and(Nat.is_eq(1n+m, n), pc.isW(f))

# owing id n: no submission yet (and n is 1), or as Kowe.at
def pc.Kowe(inbox: List<&2, C.Sub>, +n: Nat) -> Bool:
  match inbox:
    case Nil{}:
      Nat.is_eq(n, 1n)
    case s <> rest:
      match s:
        case C.Sub{+m, f}:
          pc.Kowe.at(Nat.is_eq(m, n), n, m, f)

def pc.Kph(ph: C.Ph, inbox: List<&2, C.Sub>) -> Bool:
  match ph:
    case C.Watching{w}:
      pc.empty(inbox)
    case C.Owing{k, +n}:
      pc.Kowe(inbox, n)
    case C.Ended{}:
      True{}

def pc.K(s: C.St) -> Bool:
  match s:
    case C.St{ph, cut, open, +inbox}:
      Bool.and(pc.Kph(ph, inbox), pc.Kin(inbox))

def pc.Kin_of(s: C.St, k: {pc.K(s) == True{} : Bool}) -> {pc.Kin(C.St.inbox(s)) == True{} : Bool}:
  match s:
    case C.St{ph, cut, open, +inbox}:
      pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k)

# the parts of Old(Sub{j, f} <> r, m)
def pc.old_head(+f: C.Fate, +j: Nat, +m: Nat, +r: List<&2, C.Sub>, o: {pc.Old(C.Sub{j, f} <> r, m) == True{} : Bool}) -> {pc.isW(f) == True{} : Bool}:
  pc.and_l(pc.isW(f), Bool.and(Nat.is_le(1n+j, m), pc.Old(r, j)), o)

def pc.old_lt(+f: C.Fate, +j: Nat, +m: Nat, +r: List<&2, C.Sub>, o: {pc.Old(C.Sub{j, f} <> r, m) == True{} : Bool}) -> {Nat.is_le(1n+j, m) == True{} : Bool}:
  pc.and_l(Nat.is_le(1n+j, m), pc.Old(r, j), pc.and_r(pc.isW(f), Bool.and(Nat.is_le(1n+j, m), pc.Old(r, j)), o))

def pc.old_tail(+f: C.Fate, +j: Nat, +m: Nat, +r: List<&2, C.Sub>, o: {pc.Old(C.Sub{j, f} <> r, m) == True{} : Bool}) -> {pc.Old(r, j) == True{} : Bool}:
  pc.and_r(Nat.is_le(1n+j, m), pc.Old(r, j), pc.and_r(pc.isW(f), Bool.and(Nat.is_le(1n+j, m), pc.Old(r, j)), o))

# no submission in an old list has an id m or above
def pc.old_none.at(same: Bool, +j: Nat, +n: Nat, -f: C.Fate, -r: List<&2, C.Sub>, eb: {Nat.is_eq(j, n) == same : Bool}, lt: {Nat.is_le(1n+j, n) == True{} : Bool}, ih: {None{} == C.fate(r, n) : Maybe<&2, C.Fate>}) -> {None{} == Maybe.or(&2, C.Fate, C.fate.here(same, f), C.fate(r, n)) : Maybe<&2, C.Fate>}:
  match same:
    case True{}:
      pc.lt_ne({None{} == Some{f} : Maybe<&2, C.Fate>}, j, n, lt, eb)
    case False{}:
      ih

def pc.old_none(rest: List<&2, C.Sub>, +m: Nat, +n: Nat, +o: {pc.Old(rest, m) == True{} : Bool}, +le: {Nat.is_le(m, n) == True{} : Bool}) -> {None{} == C.fate(rest, n) : Maybe<&2, C.Fate>}:
  match rest:
    case Nil{}:
      {==}
    case s <> +r:
      match s:
        case C.Sub{+j, +f}:
          pc.old_none.at(Nat.is_eq(j, n), j, n, f, r, {==}, pc.le_trans(1n+j, m, n, pc.old_lt(f, j, m, r, o), le), pc.old_none(r, j, n, pc.old_tail(f, j, m, r, o), pc.le_pred(j, n, pc.le_trans(1n+j, m, n, pc.old_lt(f, j, m, r, o), le))))

# no submission in an old list is placed or live
def pc.old_placed(rest: List<&2, C.Sub>, +m: Nat, o: {pc.Old(rest, m) == True{} : Bool}) -> {0n == C.placed(rest) : Nat}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case C.Sub{+j, f}:
          match f:
            case C.Queued{}:
              pc.absurd({0n == C.placed(C.Sub{j, C.Queued{}} <> r) : Nat}, o)
            case C.Withdrawn{}:
              pc.old_placed(r, j, pc.and_r(Nat.is_le(1n+j, m), pc.Old(r, j), o))
            case C.Placed{}:
              pc.absurd({0n == C.placed(C.Sub{j, C.Placed{}} <> r) : Nat}, o)

def pc.old_live(rest: List<&2, C.Sub>, +m: Nat, o: {pc.Old(rest, m) == True{} : Bool}) -> {0n == C.live(rest) : Nat}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case C.Sub{+j, f}:
          match f:
            case C.Queued{}:
              pc.absurd({0n == C.live(C.Sub{j, C.Queued{}} <> r) : Nat}, o)
            case C.Withdrawn{}:
              pc.old_live(r, j, pc.and_r(Nat.is_le(1n+j, m), pc.Old(r, j), o))
            case C.Placed{}:
              pc.absurd({0n == C.live(C.Sub{j, C.Placed{}} <> r) : Nat}, o)

# a delivery or withdrawal leaves a withdrawn submission withdrawn
def pc.isW_act(f: C.Fate, +a: C.Act, +i: Nat, w: {pc.isW(f) == True{} : Bool}) -> {pc.isW(C.Fate.act(a, i, f)) == True{} : Bool}:
  match f:
    case C.Queued{}:
      pc.absurd({pc.isW(C.Fate.act(a, i, C.Queued{})) == True{} : Bool}, w)
    case C.Withdrawn{}:
      {==}
    case C.Placed{}:
      pc.absurd({pc.isW(C.Fate.act(a, i, C.Placed{})) == True{} : Bool}, w)

def pc.old_act(rest: List<&2, C.Sub>, +m: Nat, +a: C.Act, +o: {pc.Old(rest, m) == True{} : Bool}) -> {pc.Old(C.act(rest, a), m) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case s <> +r:
      match s:
        case C.Sub{+j, +f}:
          pc.and_in(pc.isW(C.Fate.act(a, j, f)), Bool.and(Nat.is_le(1n+j, m), pc.Old(C.act(r, a), j)), pc.isW_act(f, a, j, pc.old_head(f, j, m, r, o)), pc.and_in(Nat.is_le(1n+j, m), pc.Old(C.act(r, a), j), pc.old_lt(f, j, m, r, o), pc.old_act(r, j, a, pc.old_tail(f, j, m, r, o))))

# ... and leaves an old list as it is
def pc.act_eq(rest: List<&2, C.Sub>, +m: Nat, +a: C.Act, o: {pc.Old(rest, m) == True{} : Bool}) -> {rest == C.act(rest, a) : List<&2, C.Sub>}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case C.Sub{+j, f}:
          match f:
            case C.Queued{}:
              pc.absurd({C.Sub{j, C.Queued{}} <> r == C.act(C.Sub{j, C.Queued{}} <> r, a) : List<&2, C.Sub>}, o)
            case C.Withdrawn{}:
              %pc.act_eq(r, j, a, pc.and_r(Nat.is_le(1n+j, m), pc.Old(r, j), o)) : {C.Sub{j, C.Withdrawn{}} <> r == C.Sub{j, C.Withdrawn{}} <> _ : List<&2, C.Sub>}
              {==}
            case C.Placed{}:
              pc.absurd({C.Sub{j, C.Placed{}} <> r == C.act(C.Sub{j, C.Placed{}} <> r, a) : List<&2, C.Sub>}, o)

# The invariant K

def pc.kat(same: Bool, +n: Nat, +m: Nat, -f: C.Fate, e: {same == True{} : Bool}) -> {pc.Kowe.at(same, n, m, f) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      pc.absurd({pc.Kowe.at(False{}, n, m, f) == True{} : Bool}, e)

# after the newest submission n is withdrawn, the task owes n + 1
def pc.kat_w(same: Bool, +m: Nat, +n: Nat, e: {Nat.is_eq(m, n) == True{} : Bool}) -> {pc.Kowe.at(same, 1n+n, m, C.Withdrawn{}) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      pc.and_in(Nat.is_eq(1n+m, 1n+n), True{}, e, {==})

def pc.kat_act(same: Bool, +n: Nat, +m: Nat, +f: C.Fate, +a: C.Act, +k: {pc.Kowe.at(same, n, m, f) == True{} : Bool}) -> {pc.Kowe.at(same, n, m, C.Fate.act(a, m, f)) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      pc.and_in(Nat.is_eq(1n+m, n), pc.isW(C.Fate.act(a, m, f)), pc.and_l(Nat.is_eq(1n+m, n), pc.isW(f), k), pc.isW_act(f, a, m, pc.and_r(Nat.is_eq(1n+m, n), pc.isW(f), k)))

# the watch hands on no submission
def pc.Kph_watched(x: C.Next) -> {pc.Kph(C.watched(x), Nil{}) == True{} : Bool}:
  match x:
    case C.Watch{w}:
      {==}
    case C.Owe{k}:
      {==}
    case C.Quiet{}:
      {==}

# the first submission
def pc.K_new0(open: Bool, +kr: C.Report, +n: Nat, kph: {Nat.is_eq(n, 1n) == True{} : Bool}) -> {pc.K(C.owe.new(open, kr, n, Nil{})) == True{} : Bool}:
  match open:
    case True{}:
      pc.and_in(pc.Kowe.at(Nat.is_eq(n, n), n, n, C.Queued{}), True{}, pc.kat(Nat.is_eq(n, n), n, n, C.Queued{}, pc.eq_refl(n)), {==})
    case False{}:
      pc.and_in(Nat.is_eq(n, 1n), True{}, kph, {==})

# a submission after the withdrawn one m
def pc.K_new(open: Bool, +kr: C.Report, +n: Nat, +m: Nat, +f: C.Fate, +rest: List<&2, C.Sub>, +kph: {Bool.and(Nat.is_eq(1n+m, n), pc.isW(f)) == True{} : Bool}, kph0: {pc.Kowe.at(Nat.is_eq(m, n), n, m, f) == True{} : Bool}, kin: {pc.Old(rest, m) == True{} : Bool}) -> {pc.K(C.owe.new(open, kr, n, C.Sub{m, f} <> rest)) == True{} : Bool}:
  match open:
    case True{}:
      pc.and_in(pc.Kowe.at(Nat.is_eq(n, n), n, n, C.Queued{}), pc.Old(C.Sub{m, f} <> rest, n), pc.kat(Nat.is_eq(n, n), n, n, C.Queued{}, pc.eq_refl(n)), pc.and_in(pc.isW(f), Bool.and(Nat.is_le(1n+m, n), pc.Old(rest, m)), pc.and_r(Nat.is_eq(1n+m, n), pc.isW(f), kph), pc.and_in(Nat.is_le(1n+m, n), pc.Old(rest, m), pc.le_of_eq(1n+m, n, pc.and_l(Nat.is_eq(1n+m, n), pc.isW(f), kph)), kin)))
    case False{}:
      pc.and_in(pc.Kowe.at(Nat.is_eq(m, n), n, m, f), pc.Old(rest, m), kph0, kin)

# the report rule on the newest submission m (same: m is the owed id n)
def pc.K_owe.at(same: Bool, +kr: C.Report, +n: Nat, +m: Nat, f: C.Fate, +rest: List<&2, C.Sub>, +open: Bool, eb: {Nat.is_eq(m, n) == same : Bool}, +kph: {pc.Kowe.at(same, n, m, f) == True{} : Bool}, +kph0: {pc.Kowe.at(Nat.is_eq(m, n), n, m, f) == True{} : Bool}, +kin: {pc.Old(rest, m) == True{} : Bool}) -> {pc.K(C.owe(Maybe.or(&2, C.Fate, C.fate.here(same, f), C.fate(rest, n)), kr, n, open, C.Sub{m, f} <> rest)) == True{} : Bool}:
  match same:
    case True{}:
      match f:
        case C.Queued{}:
          pc.and_in(pc.Kowe.at(Nat.is_eq(m, n), n, m, C.Queued{}), pc.Old(rest, m), kph0, kin)
        case C.Withdrawn{}:
          pc.and_in(pc.Kowe.at(Nat.is_eq(m, 1n+n), 1n+n, m, C.Withdrawn{}), pc.Old(rest, m), pc.kat_w(Nat.is_eq(m, 1n+n), m, n, eb), kin)
        case C.Placed{}:
          kin
    case False{}:
      %pc.old_none(rest, m, n, kin, pc.le_pred(m, n, pc.le_of_eq(1n+m, n, pc.and_l(Nat.is_eq(1n+m, n), pc.isW(f), kph)))) : {pc.K(C.owe(_, kr, n, open, C.Sub{m, f} <> rest)) == True{} : Bool}
      pc.K_new(open, kr, n, m, f, rest, kph, kph0, kin)

# the report rule keeps K
def pc.K_owe(inbox: List<&2, C.Sub>, +kr: C.Report, +n: Nat, +open: Bool, +kph: {pc.Kowe(inbox, n) == True{} : Bool}, kin: {pc.Kin(inbox) == True{} : Bool}) -> {pc.K(C.owe(C.fate(inbox, n), kr, n, open, inbox)) == True{} : Bool}:
  match inbox:
    case Nil{}:
      pc.K_new0(open, kr, n, kph)
    case s <> rest:
      match s:
        case C.Sub{+m, f}:
          pc.K_owe.at(Nat.is_eq(m, n), kr, n, m, f, rest, open, {==}, kph, kph, kin)

# the abort keeps K: a delete of a watched child owes report 1, which has
# no submission yet
def pc.K_cut(ph: C.Ph, del: Bool, +inbox: List<&2, C.Sub>, +open: Bool, kph: {pc.Kph(ph, inbox) == True{} : Bool}, kin: {pc.Kin(inbox) == True{} : Bool}) -> {pc.K(C.St{C.cut.ph(ph, del), None{}, open, inbox}) == True{} : Bool}:
  match ph:
    case C.Watching{w}:
      match del:
        case True{}:
          match inbox:
            case Nil{}:
              {==}
            case s <> rest:
              pc.absurd({pc.K(C.St{C.Owing{C.Cancelled{}, 1n}, None{}, open, s <> rest}) == True{} : Bool}, kph)
        case False{}:
          kin
    case C.Owing{kr, +n}:
      pc.and_in(pc.Kowe(inbox, n), pc.Kin(inbox), kph, kin)
    case C.Ended{}:
      kin

def pc.K_poll(cut: Maybe<&2, Bool>, ph: C.Ph, +inbox: List<&2, C.Sub>, +open: Bool, +cfg: C.Cfg, +dt: Nat, +o: C.Obs, +kph: {pc.Kph(ph, inbox) == True{} : Bool}, +kin: {pc.Kin(inbox) == True{} : Bool}) -> {pc.K(C.task(cfg, ph, cut, open, inbox, dt, o)) == True{} : Bool}:
  match cut:
    case None{}:
      match ph:
        case C.Watching{+w}:
          match inbox:
            case Nil{}:
              pc.and_in(pc.Kph(C.watched(C.look(cfg, w, 1n+dt, o)), Nil{}), True{}, pc.Kph_watched(C.look(cfg, w, 1n+dt, o)), {==})
            case s <> rest:
              pc.absurd({pc.K(C.task(cfg, C.Watching{w}, None{}, open, s <> rest, dt, o)) == True{} : Bool}, kph)
        case C.Owing{kr, +n}:
          pc.K_owe(inbox, kr, n, open, kph, kin)
        case C.Ended{}:
          kin
    case Some{del}:
      pc.K_cut(ph, del, inbox, open, kph, kin)

# a delivery or withdrawal keeps K: it touches the newest submission only
def pc.K_act(inbox: List<&2, C.Sub>, ph: C.Ph, +a: C.Act, +kph: {pc.Kph(ph, inbox) == True{} : Bool}, +kin: {pc.Kin(inbox) == True{} : Bool}) -> {Bool.and(pc.Kph(ph, C.act(inbox, a)), pc.Kin(C.act(inbox, a))) == True{} : Bool}:
  match inbox:
    case Nil{}:
      pc.and_in(pc.Kph(ph, Nil{}), True{}, kph, {==})
    case s <> +rest:
      match s:
        case C.Sub{+m, +f}:
          match ph:
            case C.Watching{w}:
              pc.absurd({Bool.and(pc.Kph(C.Watching{w}, C.act(C.Sub{m, f} <> rest, a)), pc.Kin(C.act(C.Sub{m, f} <> rest, a))) == True{} : Bool}, kph)
            case C.Owing{kr, +n}:
              pc.and_in(pc.Kowe.at(Nat.is_eq(m, n), n, m, C.Fate.act(a, m, f)), pc.Old(C.act(rest, a), m), pc.kat_act(Nat.is_eq(m, n), n, m, f, a, kph), pc.old_act(rest, m, a, kin))
            case C.Ended{}:
              pc.old_act(rest, m, a, kin)

# every event keeps K
def pc.K_step(+cfg: C.Cfg, s: C.St, e: C.Ev, +k: {pc.K(s) == True{} : Bool}) -> {pc.K(C.step(cfg, s, e)) == True{} : Bool}:
  match s:
    case C.St{+ph, +cut, +open, +inbox}:
      match e:
        case C.Poll{+dt, +o}:
          pc.K_poll(cut, ph, inbox, open, cfg, dt, o, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case C.Deliver{+m}:
          pc.K_act(inbox, ph, C.Place{m}, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case C.Withdraw{+m}:
          pc.K_act(inbox, ph, C.Pull{m}, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case C.Abort{}:
          pc.K_act(inbox, ph, C.PullAll{}, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case C.Shut{}:
          pc.K_act(inbox, ph, C.PullAll{}, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case C.Reopen{}:
          k
        case C.Cut{del}:
          k

def pc.K_run(evs: List<&2, C.Ev>, +cfg: C.Cfg, +s: C.St, k: {pc.K(s) == True{} : Bool}) -> {pc.K(C.run(evs, cfg, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      k
    case +e <> t:
      pc.K_run(t, cfg, C.step(cfg, s, e), pc.K_step(cfg, s, e, k))

# one_live, report_once: only the newest submission may be live
def pc.le1_live(f: C.Fate) -> {Nat.is_le(Nat.add(C.Fate.live(f), 0n), 1n) == True{} : Bool}:
  match f:
    case C.Queued{}:
      {==}
    case C.Withdrawn{}:
      {==}
    case C.Placed{}:
      {==}

def pc.le1_placed(f: C.Fate) -> {Nat.is_le(Nat.add(C.Fate.placed(f), 0n), 1n) == True{} : Bool}:
  match f:
    case C.Queued{}:
      {==}
    case C.Withdrawn{}:
      {==}
    case C.Placed{}:
      {==}

def pc.live_le(inbox: List<&2, C.Sub>, kin: {pc.Kin(inbox) == True{} : Bool}) -> {Nat.is_le(C.live(inbox), 1n) == True{} : Bool}:
  match inbox:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case C.Sub{+m, f}:
          %pc.old_live(rest, m, kin) : {Nat.is_le(Nat.add(C.Fate.live(f), _), 1n) == True{} : Bool}
          pc.le1_live(f)

def pc.placed_le(inbox: List<&2, C.Sub>, kin: {pc.Kin(inbox) == True{} : Bool}) -> {Nat.is_le(C.placed(inbox), 1n) == True{} : Bool}:
  match inbox:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case C.Sub{+m, f}:
          %pc.old_placed(rest, m, kin) : {Nat.is_le(Nat.add(C.Fate.placed(f), _), 1n) == True{} : Bool}
          pc.le1_placed(f)

def pc.one_live(+cfg: C.Cfg, +evs: List<&2, C.Ev>) -> {Nat.is_le(C.live(C.St.inbox(C.run(evs, cfg, C.St.init(cfg)))), 1n) == True{} : Bool}:
  pc.live_le(C.St.inbox(C.run(evs, cfg, C.St.init(cfg))), pc.Kin_of(C.run(evs, cfg, C.St.init(cfg)), pc.K_run(evs, cfg, C.St.init(cfg), {==})))

def pc.report_once(+cfg: C.Cfg, +evs: List<&2, C.Ev>) -> {Nat.is_le(C.St.placed(C.run(evs, cfg, C.St.init(cfg))), 1n) == True{} : Bool}:
  pc.placed_le(C.St.inbox(C.run(evs, cfg, C.St.init(cfg))), pc.Kin_of(C.run(evs, cfg, C.St.init(cfg)), pc.K_run(evs, cfg, C.St.init(cfg), {==})))

# resubmits_per_abort: the potential pot = 1 + the withdrawn submissions
# bounds the inbox (all but the newest are withdrawn) and grows only at a
# withdrawal (only the newest may be queued)
def pc.fwd(f: C.Fate) -> Nat:
  match f:
    case C.Queued{}:
      0n
    case C.Withdrawn{}:
      1n
    case C.Placed{}:
      0n

def pc.slots(inbox: List<&2, C.Sub>) -> Nat:
  match inbox:
    case Nil{}:
      1n
    case s <> rest:
      match s:
        case C.Sub{i, f}:
          Nat.add(pc.fwd(f), pc.slots(rest))

def pc.pot(s: C.St) -> Nat:
  pc.slots(C.St.inbox(s))

def pc.acut(a: C.Act) -> Nat:
  match a:
    case C.Place{m}:
      0n
    case C.Pull{m}:
      1n
    case C.PullAll{}:
      1n

def pc.old_len(rest: List<&2, C.Sub>, +m: Nat, o: {pc.Old(rest, m) == True{} : Bool}) -> {Nat.is_le(1n+List.length(&2, C.Sub, rest), pc.slots(rest)) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case C.Sub{+j, f}:
          match f:
            case C.Queued{}:
              pc.absurd({Nat.is_le(1n+List.length(&2, C.Sub, C.Sub{j, C.Queued{}} <> r), pc.slots(C.Sub{j, C.Queued{}} <> r)) == True{} : Bool}, o)
            case C.Withdrawn{}:
              pc.old_len(r, j, pc.and_r(Nat.is_le(1n+j, m), pc.Old(r, j), o))
            case C.Placed{}:
              pc.absurd({Nat.is_le(1n+List.length(&2, C.Sub, C.Sub{j, C.Placed{}} <> r), pc.slots(C.Sub{j, C.Placed{}} <> r)) == True{} : Bool}, o)

def pc.len_le(inbox: List<&2, C.Sub>, kin: {pc.Kin(inbox) == True{} : Bool}) -> {Nat.is_le(List.length(&2, C.Sub, inbox), pc.slots(inbox)) == True{} : Bool}:
  match inbox:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case C.Sub{+m, +f}:
          pc.le_trans(1n+List.length(&2, C.Sub, rest), pc.slots(rest), Nat.add(pc.fwd(f), pc.slots(rest)), pc.old_len(rest, m, kin), pc.le_add(pc.fwd(f), pc.slots(rest)))

def pc.hit_placed(b: Bool, +w: Nat) -> {Nat.is_le(Nat.add(pc.fwd(C.Act.hit(b, C.Placed{})), w), w) == True{} : Bool}:
  match b:
    case True{}:
      pc.le_refl(w)
    case False{}:
      pc.le_refl(w)

def pc.hit_pulled(b: Bool, +w: Nat) -> {Nat.is_le(Nat.add(pc.fwd(C.Act.hit(b, C.Withdrawn{})), w), 1n+w) == True{} : Bool}:
  match b:
    case True{}:
      pc.le_refl(w)
    case False{}:
      pc.le_succ(w, w, pc.le_refl(w))

def pc.slots_queued(a: C.Act, +i: Nat, +w: Nat) -> {Nat.is_le(Nat.add(pc.fwd(C.Act.queued(a, i)), w), Nat.add(pc.acut(a), Nat.add(0n, w))) == True{} : Bool}:
  match a:
    case C.Place{+x}:
      pc.hit_placed(Nat.is_eq(i, x), w)
    case C.Pull{+x}:
      pc.hit_pulled(Nat.is_eq(i, x), w)
    case C.PullAll{}:
      pc.le_refl(w)

# the newest submission's share of the potential grows by at most the act's
def pc.slots_head(f: C.Fate, +a: C.Act, +i: Nat, +w: Nat) -> {Nat.is_le(Nat.add(pc.fwd(C.Fate.act(a, i, f)), w), Nat.add(pc.acut(a), Nat.add(pc.fwd(f), w))) == True{} : Bool}:
  match f:
    case C.Queued{}:
      pc.slots_queued(a, i, w)
    case C.Withdrawn{}:
      pc.le_add(pc.acut(a), Nat.add(1n, w))
    case C.Placed{}:
      pc.le_add(pc.acut(a), w)

def pc.slots_act(inbox: List<&2, C.Sub>, +a: C.Act, kin: {pc.Kin(inbox) == True{} : Bool}) -> {Nat.is_le(pc.slots(C.act(inbox, a)), Nat.add(pc.acut(a), pc.slots(inbox))) == True{} : Bool}:
  match inbox:
    case Nil{}:
      pc.le_add(pc.acut(a), 1n)
    case s <> +rest:
      match s:
        case C.Sub{+m, +f}:
          %pc.act_eq(rest, m, a, kin) : {Nat.is_le(Nat.add(pc.fwd(C.Fate.act(a, m, f)), pc.slots(_)), Nat.add(pc.acut(a), Nat.add(pc.fwd(f), pc.slots(rest)))) == True{} : Bool}
          pc.slots_head(f, a, m, pc.slots(rest))

def pc.slots_owe(x: Maybe<&2, C.Fate>, +kr: C.Report, +n: Nat, open: Bool, +inbox: List<&2, C.Sub>) -> {Nat.is_le(pc.slots(C.St.inbox(C.owe(x, kr, n, open, inbox))), pc.slots(inbox)) == True{} : Bool}:
  match x:
    case None{}:
      match open:
        case True{}:
          pc.le_refl(pc.slots(inbox))
        case False{}:
          pc.le_refl(pc.slots(inbox))
    case Some{y}:
      match y:
        case C.Queued{}:
          pc.le_refl(pc.slots(inbox))
        case C.Withdrawn{}:
          pc.le_refl(pc.slots(inbox))
        case C.Placed{}:
          pc.le_refl(pc.slots(inbox))

def pc.slots_poll(cut: Maybe<&2, Bool>, ph: C.Ph, +inbox: List<&2, C.Sub>, +open: Bool, +cfg: C.Cfg, +dt: Nat, +o: C.Obs) -> {Nat.is_le(pc.slots(C.St.inbox(C.task(cfg, ph, cut, open, inbox, dt, o))), pc.slots(inbox)) == True{} : Bool}:
  match cut:
    case None{}:
      match ph:
        case C.Watching{w}:
          pc.le_refl(pc.slots(inbox))
        case C.Owing{kr, +n}:
          pc.slots_owe(C.fate(inbox, n), kr, n, open, inbox)
        case C.Ended{}:
          pc.le_refl(pc.slots(inbox))
    case Some{del}:
      pc.le_refl(pc.slots(inbox))

def pc.pot_step(+cfg: C.Cfg, s: C.St, e: C.Ev, k: {pc.K(s) == True{} : Bool}) -> {Nat.is_le(pc.pot(C.step(cfg, s, e)), Nat.add(C.Ev.cut(e), pc.pot(s))) == True{} : Bool}:
  match s:
    case C.St{+ph, +cut, +open, +inbox}:
      match e:
        case C.Poll{+dt, +o}:
          pc.slots_poll(cut, ph, inbox, open, cfg, dt, o)
        case C.Deliver{+m}:
          pc.slots_act(inbox, C.Place{m}, pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case C.Withdraw{+m}:
          pc.slots_act(inbox, C.Pull{m}, pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case C.Abort{}:
          pc.slots_act(inbox, C.PullAll{}, pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case C.Shut{}:
          pc.slots_act(inbox, C.PullAll{}, pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case C.Reopen{}:
          pc.le_refl(pc.slots(inbox))
        case C.Cut{del}:
          pc.le_refl(pc.slots(inbox))

def pc.pot_run(evs: List<&2, C.Ev>, +cfg: C.Cfg, +s: C.St, +k: {pc.K(s) == True{} : Bool}) -> {Nat.is_le(pc.pot(C.run(evs, cfg, s)), Nat.add(C.cuts(evs), pc.pot(s))) == True{} : Bool}:
  match evs:
    case Nil{}:
      pc.le_refl(pc.pot(s))
    case +e <> +t:
      %Equal.sym(Nat, Nat.add(Nat.add(C.cuts(t), C.Ev.cut(e)), pc.pot(s)), Nat.add(C.cuts(t), Nat.add(C.Ev.cut(e), pc.pot(s))), pc.add_assoc(C.cuts(t), C.Ev.cut(e), pc.pot(s))) : {Nat.is_le(pc.pot(C.run(t, cfg, C.step(cfg, s, e))), _) == True{} : Bool}
      pc.le_trans(pc.pot(C.run(t, cfg, C.step(cfg, s, e))), Nat.add(C.cuts(t), pc.pot(C.step(cfg, s, e))), Nat.add(C.cuts(t), Nat.add(C.Ev.cut(e), pc.pot(s))), pc.pot_run(t, cfg, C.step(cfg, s, e), pc.K_step(cfg, s, e, k)), pc.le_add_mono(C.cuts(t), pc.pot(C.step(cfg, s, e)), Nat.add(C.Ev.cut(e), pc.pot(s)), pc.pot_step(cfg, s, e, k)))

def pc.resubmits_per_abort(+cfg: C.Cfg, +evs: List<&2, C.Ev>) -> {Nat.is_le(List.length(&2, C.Sub, C.St.inbox(C.run(evs, cfg, C.St.init(cfg)))), Nat.add(C.cuts(evs), 1n)) == True{} : Bool}:
  pc.le_trans(List.length(&2, C.Sub, C.St.inbox(C.run(evs, cfg, C.St.init(cfg)))), pc.pot(C.run(evs, cfg, C.St.init(cfg))), Nat.add(C.cuts(evs), 1n), pc.len_le(C.St.inbox(C.run(evs, cfg, C.St.init(cfg))), pc.Kin_of(C.run(evs, cfg, C.St.init(cfg)), pc.K_run(evs, cfg, C.St.init(cfg), {==}))), pc.pot_run(evs, cfg, C.St.init(cfg), {==}))

# delivered_once: `soon` holds when the open, unmarked task owes id n with
# no submission of n yet or n queued, or the report is placed; `ready`
# when n is queued, or the report is placed
def pc.unmarked(cut: Maybe<&2, Bool>) -> Bool:
  match cut:
    case None{}:
      True{}
    case Some{d}:
      False{}

def pc.fq(x: Maybe<&2, C.Fate>) -> Bool:
  match x:
    case None{}:
      False{}
    case Some{f}:
      match f:
        case C.Queued{}:
          True{}
        case C.Withdrawn{}:
          False{}
        case C.Placed{}:
          False{}

def pc.fs(x: Maybe<&2, C.Fate>) -> Bool:
  match x:
    case None{}:
      True{}
    case Some{f}:
      match f:
        case C.Queued{}:
          True{}
        case C.Withdrawn{}:
          False{}
        case C.Placed{}:
          False{}

def pc.ready(s: C.St) -> Bool:
  match s:
    case C.St{ph, cut, open, +inbox}:
      match ph:
        case C.Watching{w}:
          False{}
        case C.Owing{k, +n}:
          Bool.and(pc.unmarked(cut), Bool.and(open, pc.fq(C.fate(inbox, n))))
        case C.Ended{}:
          Nat.is_eq(C.placed(inbox), 1n)

def pc.soon(s: C.St) -> Bool:
  match s:
    case C.St{ph, cut, open, +inbox}:
      match ph:
        case C.Watching{w}:
          False{}
        case C.Owing{k, +n}:
          Bool.and(pc.unmarked(cut), Bool.and(open, pc.fs(C.fate(inbox, n))))
        case C.Ended{}:
          Nat.is_eq(C.placed(inbox), 1n)

# the submission just made is found queued
def pc.fs_new(same: Bool, -x: Maybe<&2, C.Fate>, e: {same == True{} : Bool}) -> {pc.fs(Maybe.or(&2, C.Fate, C.fate.here(same, C.Queued{}), x)) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      pc.absurd({pc.fs(Maybe.or(&2, C.Fate, C.fate.here(False{}, C.Queued{}), x)) == True{} : Bool}, e)

def pc.fq_new(same: Bool, -x: Maybe<&2, C.Fate>, e: {same == True{} : Bool}) -> {pc.fq(Maybe.or(&2, C.Fate, C.fate.here(same, C.Queued{}), x)) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      pc.absurd({pc.fq(Maybe.or(&2, C.Fate, C.fate.here(False{}, C.Queued{}), x)) == True{} : Bool}, e)

def pc.fs_off(same: Bool, -f: C.Fate, e: {same == False{} : Bool}) -> {pc.fs(Maybe.or(&2, C.Fate, C.fate.here(same, f), None{})) == True{} : Bool}:
  match same:
    case True{}:
      pc.absurd({pc.fs(Maybe.or(&2, C.Fate, C.fate.here(True{}, f), None{})) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, e))
    case False{}:
      {==}

def pc.fs_of_fq(x: Maybe<&2, C.Fate>, e: {pc.fq(x) == True{} : Bool}) -> {pc.fs(x) == True{} : Bool}:
  match x:
    case None{}:
      pc.absurd({pc.fs(None{}) == True{} : Bool}, e)
    case Some{f}:
      match f:
        case C.Queued{}:
          {==}
        case C.Withdrawn{}:
          pc.absurd({pc.fs(Some{C.Withdrawn{}}) == True{} : Bool}, e)
        case C.Placed{}:
          pc.absurd({pc.fs(Some{C.Placed{}}) == True{} : Bool}, e)

# no queued submission where none exists
def pc.fq_none(-A: Type, x: Maybe<&2, C.Fate>, e: {None{} == x : Maybe<&2, C.Fate>}, r: {pc.fq(x) == True{} : Bool}) -> A:
  match x:
    case None{}:
      pc.absurd(A, r)
    case Some{f}:
      pc.none_some(A, f, e)

# one step of the report rule from K leaves the report soon
def pc.soon_owe.at(same: Bool, +kr: C.Report, +n: Nat, +m: Nat, f: C.Fate, +rest: List<&2, C.Sub>, +eb: {Nat.is_eq(m, n) == same : Bool}, kph: {pc.Kowe.at(same, n, m, f) == True{} : Bool}, +kin: {pc.Old(rest, m) == True{} : Bool}) -> {pc.soon(C.owe(Maybe.or(&2, C.Fate, C.fate.here(same, f), C.fate(rest, n)), kr, n, True{}, C.Sub{m, f} <> rest)) == True{} : Bool}:
  match same:
    case True{}:
      match f:
        case C.Queued{}:
          pc.fs_new(Nat.is_eq(m, n), C.fate(rest, n), eb)
        case C.Withdrawn{}:
          %pc.old_none(rest, m, 1n+n, kin, pc.le_succ(m, n, pc.le_of_eq(m, n, eb))) : {pc.fs(Maybe.or(&2, C.Fate, C.fate.here(Nat.is_eq(m, 1n+n), C.Withdrawn{}), _)) == True{} : Bool}
          pc.fs_off(Nat.is_eq(m, 1n+n), C.Withdrawn{}, pc.eq_next(m, n, eb))
        case C.Placed{}:
          %pc.old_placed(rest, m, kin) : {Nat.is_eq(Nat.add(1n, _), 1n) == True{} : Bool}
          {==}
    case False{}:
      %pc.old_none(rest, m, n, kin, pc.le_pred(m, n, pc.le_of_eq(1n+m, n, pc.and_l(Nat.is_eq(1n+m, n), pc.isW(f), kph)))) : {pc.soon(C.owe(_, kr, n, True{}, C.Sub{m, f} <> rest)) == True{} : Bool}
      pc.fs_new(Nat.is_eq(n, n), C.fate(C.Sub{m, f} <> rest, n), pc.eq_refl(n))

def pc.soon_owe(inbox: List<&2, C.Sub>, +kr: C.Report, +n: Nat, kph: {pc.Kowe(inbox, n) == True{} : Bool}, kin: {pc.Kin(inbox) == True{} : Bool}) -> {pc.soon(C.owe(C.fate(inbox, n), kr, n, True{}, inbox)) == True{} : Bool}:
  match inbox:
    case Nil{}:
      pc.fs_new(Nat.is_eq(n, n), None{}, pc.eq_refl(n))
    case s <> rest:
      match s:
        case C.Sub{+m, f}:
          pc.soon_owe.at(Nat.is_eq(m, n), kr, n, m, f, rest, {==}, kph, kin)

# a soon report is ready after one more task step
def pc.ready_owe(x: Maybe<&2, C.Fate>, +kr: C.Report, +n: Nat, +inbox: List<&2, C.Sub>, ex: {C.fate(inbox, n) == x : Maybe<&2, C.Fate>}, sn: {pc.fs(x) == True{} : Bool}) -> {pc.ready(C.owe(x, kr, n, True{}, inbox)) == True{} : Bool}:
  match x:
    case None{}:
      pc.fq_new(Nat.is_eq(n, n), C.fate(inbox, n), pc.eq_refl(n))
    case Some{y}:
      match y:
        case C.Queued{}:
          %Equal.sym(Maybe<&2, C.Fate>, C.fate(inbox, n), Some{C.Queued{}}, ex) : {pc.fq(_) == True{} : Bool}
          {==}
        case C.Withdrawn{}:
          pc.absurd({pc.ready(C.owe(Some{C.Withdrawn{}}, kr, n, True{}, inbox)) == True{} : Bool}, sn)
        case C.Placed{}:
          pc.absurd({pc.ready(C.owe(Some{C.Placed{}}, kr, n, True{}, inbox)) == True{} : Bool}, sn)

def pc.ready_soon(+cfg: C.Cfg, s: C.St, +d: Nat, +o: C.Obs, sn: {pc.soon(s) == True{} : Bool}) -> {pc.ready(C.step(cfg, s, C.Poll{d, o})) == True{} : Bool}:
  match s:
    case C.St{ph, cut, open, +inbox}:
      match ph:
        case C.Watching{w}:
          pc.absurd({pc.ready(C.step(cfg, C.St{C.Watching{w}, cut, open, inbox}, C.Poll{d, o})) == True{} : Bool}, sn)
        case C.Owing{kr, +n}:
          match cut:
            case None{}:
              match open:
                case True{}:
                  pc.ready_owe(C.fate(inbox, n), kr, n, inbox, {==}, sn)
                case False{}:
                  pc.absurd({pc.ready(C.step(cfg, C.St{C.Owing{kr, n}, None{}, False{}, inbox}, C.Poll{d, o})) == True{} : Bool}, sn)
            case Some{del}:
              pc.absurd({pc.ready(C.step(cfg, C.St{C.Owing{kr, n}, Some{del}, open, inbox}, C.Poll{d, o})) == True{} : Bool}, sn)
        case C.Ended{}:
          match cut:
            case None{}:
              sn
            case Some{del}:
              sn

def pc.soon_of_ready(s: C.St, r: {pc.ready(s) == True{} : Bool}) -> {pc.soon(s) == True{} : Bool}:
  match s:
    case C.St{ph, cut, open, +inbox}:
      match ph:
        case C.Watching{w}:
          r
        case C.Owing{k, +n}:
          match cut:
            case None{}:
              match open:
                case True{}:
                  pc.fs_of_fq(C.fate(inbox, n), r)
                case False{}:
                  r
            case Some{d}:
              r
        case C.Ended{}:
          r

# a delivery of the queued submission n places it: one entry placed
def pc.del_at(same: Bool, +n: Nat, +m: Nat, f: C.Fate, +rest: List<&2, C.Sub>, eb: {Nat.is_eq(m, n) == same : Bool}, kph: {pc.Kowe.at(same, n, m, f) == True{} : Bool}, +kin: {pc.Old(rest, m) == True{} : Bool}, r: {pc.fq(Maybe.or(&2, C.Fate, C.fate.here(same, f), C.fate(rest, n))) == True{} : Bool}) -> {C.placed(C.act(C.Sub{m, f} <> rest, C.Place{n})) == 1n : Nat}:
  match same:
    case True{}:
      match f:
        case C.Queued{}:
          %pc.old_placed(C.act(rest, C.Place{n}), m, pc.old_act(rest, m, C.Place{n}, kin)) : {Nat.add(C.Fate.placed(C.Act.hit(Nat.is_eq(m, n), C.Placed{})), _) == 1n : Nat}
          %Equal.sym(Bool, Nat.is_eq(m, n), True{}, eb) : {Nat.add(C.Fate.placed(C.Act.hit(_, C.Placed{})), 0n) == 1n : Nat}
          {==}
        case C.Withdrawn{}:
          pc.absurd({C.placed(C.act(C.Sub{m, C.Withdrawn{}} <> rest, C.Place{n})) == 1n : Nat}, r)
        case C.Placed{}:
          pc.absurd({C.placed(C.act(C.Sub{m, C.Placed{}} <> rest, C.Place{n})) == 1n : Nat}, r)
    case False{}:
      pc.fq_none({C.placed(C.act(C.Sub{m, f} <> rest, C.Place{n})) == 1n : Nat}, C.fate(rest, n), pc.old_none(rest, m, n, kin, pc.le_pred(m, n, pc.le_of_eq(1n+m, n, pc.and_l(Nat.is_eq(1n+m, n), pc.isW(f), kph)))), r)

# a delivery of any id leaves a placed report placed once
def pc.del_end(inbox: List<&2, C.Sub>, +x: Nat, kin: {pc.Kin(inbox) == True{} : Bool}, r: {Nat.is_eq(C.placed(inbox), 1n) == True{} : Bool}) -> {C.placed(C.act(inbox, C.Place{x})) == 1n : Nat}:
  match inbox:
    case Nil{}:
      pc.absurd({C.placed(C.act(Nil{}, C.Place{x})) == 1n : Nat}, r)
    case s <> +rest:
      match s:
        case C.Sub{+m, f}:
          match f:
            case C.Queued{}:
              pc.one_zero({C.placed(C.act(C.Sub{m, C.Queued{}} <> rest, C.Place{x})) == 1n : Nat}, C.placed(rest), pc.old_placed(rest, m, kin), r)
            case C.Withdrawn{}:
              pc.one_zero({C.placed(C.act(C.Sub{m, C.Withdrawn{}} <> rest, C.Place{x})) == 1n : Nat}, C.placed(rest), pc.old_placed(rest, m, kin), r)
            case C.Placed{}:
              %pc.old_placed(C.act(rest, C.Place{x}), m, pc.old_act(rest, m, C.Place{x}, kin)) : {Nat.add(1n, _) == 1n : Nat}
              {==}

def pc.ready_deliver0(+cfg: C.Cfg, s: C.St, +k: {pc.K(s) == True{} : Bool}, r: {pc.ready(s) == True{} : Bool}) -> {C.St.placed(C.step(cfg, s, C.Deliver{C.St.owed(s)})) == 1n : Nat}:
  match s:
    case C.St{ph, cut, open, +inbox}:
      match ph:
        case C.Watching{w}:
          pc.absurd({C.St.placed(C.step(cfg, C.St{C.Watching{w}, cut, open, inbox}, C.Deliver{0n})) == 1n : Nat}, r)
        case C.Owing{kr, +n}:
          match cut:
            case None{}:
              match open:
                case True{}:
                  match inbox:
                    case Nil{}:
                      pc.absurd({C.St.placed(C.step(cfg, C.St{C.Owing{kr, n}, None{}, True{}, Nil{}}, C.Deliver{n})) == 1n : Nat}, r)
                    case s2 <> +rest:
                      match s2:
                        case C.Sub{+m, +f}:
                          pc.del_at(Nat.is_eq(m, n), n, m, f, rest, {==}, pc.and_l(pc.Kowe.at(Nat.is_eq(m, n), n, m, f), pc.Old(rest, m), k), pc.and_r(pc.Kowe.at(Nat.is_eq(m, n), n, m, f), pc.Old(rest, m), k), r)
                case False{}:
                  pc.absurd({C.St.placed(C.step(cfg, C.St{C.Owing{kr, n}, None{}, False{}, inbox}, C.Deliver{n})) == 1n : Nat}, r)
            case Some{del}:
              pc.absurd({C.St.placed(C.step(cfg, C.St{C.Owing{kr, n}, Some{del}, open, inbox}, C.Deliver{n})) == 1n : Nat}, r)
        case C.Ended{}:
          pc.del_end(inbox, 0n, k, r)

def pc.ready_deliver(+cfg: C.Cfg, +s: C.St, +m: Nat, k: {pc.K(s) == True{} : Bool}, r: {pc.ready(s) == True{} : Bool}, em: {C.St.owed(s) == m : Nat}) -> {C.St.placed(C.step(cfg, s, C.Deliver{m})) == 1n : Nat}:
  %em : {C.St.placed(C.step(cfg, s, C.Deliver{_})) == 1n : Nat}
  pc.ready_deliver0(cfg, s, k, r)

# from any state that owes the report: a reopen, three task steps (the
# first may run a pending abort, which hands the report on), and a
# delivery of the id the task then owes place it, exactly once
def pc.delivered(+cfg: C.Cfg, s: C.St, +d1: Nat, +o1: C.Obs, +d2: Nat, +o2: C.Obs, +d3: Nat, +o3: C.Obs, +m: Nat, +k: {pc.K(s) == True{} : Bool}, ow: {C.Ph.owing(C.St.ph(s)) == True{} : Bool}, em: {C.St.owed(C.run([C.Reopen{}, C.Poll{d1, o1}, C.Poll{d2, o2}, C.Poll{d3, o3}], cfg, s)) == m : Nat}) -> {C.St.placed(C.run([C.Reopen{}, C.Poll{d1, o1}, C.Poll{d2, o2}, C.Poll{d3, o3}, C.Deliver{m}], cfg, s)) == 1n : Nat}:
  match s:
    case C.St{ph, cut, open, +inbox}:
      match ph:
        case C.Watching{w}:
          pc.absurd({C.St.placed(C.run([C.Reopen{}, C.Poll{d1, o1}, C.Poll{d2, o2}, C.Poll{d3, o3}, C.Deliver{m}], cfg, C.St{C.Watching{w}, cut, open, inbox})) == 1n : Nat}, ow)
        case C.Owing{+kr, +n}:
          match cut:
            case None{}:
              pc.ready_deliver(cfg, C.step(cfg, C.step(cfg, C.owe(C.fate(inbox, n), kr, n, True{}, inbox), C.Poll{d2, o2}), C.Poll{d3, o3}), m, pc.K_step(cfg, C.step(cfg, C.owe(C.fate(inbox, n), kr, n, True{}, inbox), C.Poll{d2, o2}), C.Poll{d3, o3}, pc.K_step(cfg, C.owe(C.fate(inbox, n), kr, n, True{}, inbox), C.Poll{d2, o2}, pc.K_step(cfg, C.St{C.Owing{kr, n}, None{}, True{}, inbox}, C.Poll{d1, o1}, k))), pc.ready_soon(cfg, C.step(cfg, C.owe(C.fate(inbox, n), kr, n, True{}, inbox), C.Poll{d2, o2}), d3, o3, pc.soon_of_ready(C.step(cfg, C.owe(C.fate(inbox, n), kr, n, True{}, inbox), C.Poll{d2, o2}), pc.ready_soon(cfg, C.owe(C.fate(inbox, n), kr, n, True{}, inbox), d2, o2, pc.soon_owe(inbox, kr, n, pc.and_l(pc.Kowe(inbox, n), pc.Kin(inbox), k), pc.and_r(pc.Kowe(inbox, n), pc.Kin(inbox), k))))), em)
            case Some{del}:
              pc.ready_deliver(cfg, C.step(cfg, C.owe(C.fate(inbox, n), kr, n, True{}, inbox), C.Poll{d3, o3}), m, pc.K_step(cfg, C.owe(C.fate(inbox, n), kr, n, True{}, inbox), C.Poll{d3, o3}, pc.K_step(cfg, C.St{C.Owing{kr, n}, None{}, True{}, inbox}, C.Poll{d2, o2}, k)), pc.ready_soon(cfg, C.owe(C.fate(inbox, n), kr, n, True{}, inbox), d3, o3, pc.soon_owe(inbox, kr, n, pc.and_l(pc.Kowe(inbox, n), pc.Kin(inbox), k), pc.and_r(pc.Kowe(inbox, n), pc.Kin(inbox), k))), em)
        case C.Ended{}:
          pc.absurd({C.St.placed(C.run([C.Reopen{}, C.Poll{d1, o1}, C.Poll{d2, o2}, C.Poll{d3, o3}, C.Deliver{m}], cfg, C.St{C.Ended{}, cut, open, inbox})) == 1n : Nat}, ow)

def pc.delivered_once(+cfg: C.Cfg, +evs: List<&2, C.Ev>, +d1: Nat, +o1: C.Obs, +d2: Nat, +o2: C.Obs, +d3: Nat, +o3: C.Obs, ow: {C.Ph.owing(C.St.ph(C.run(evs, cfg, C.St.init(cfg)))) == True{} : Bool}, +m: Nat, em: {C.St.owed(C.run([C.Reopen{}, C.Poll{d1, o1}, C.Poll{d2, o2}, C.Poll{d3, o3}], cfg, C.run(evs, cfg, C.St.init(cfg)))) == m : Nat}) -> {C.St.placed(C.run([C.Reopen{}, C.Poll{d1, o1}, C.Poll{d2, o2}, C.Poll{d3, o3}, C.Deliver{m}], cfg, C.run(evs, cfg, C.St.init(cfg)))) == 1n : Nat}:
  pc.delivered(cfg, C.run(evs, cfg, C.St.init(cfg)), d1, o1, d2, o2, d3, o3, m, pc.K_run(evs, cfg, C.St.init(cfg), {==}), ow, em)
