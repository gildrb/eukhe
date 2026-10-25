# eukhe: lemmas of the lease term laws (laws/lease.bend, "The model's terms,
# pinned"): each model term against the laws' Bool, both ways.

import Base
import ../../../bend/lease.bend as Ls
import ../../../laws/lease.bend as Lease
import ../../base/logic/logic.bend as LLogicLogic

# Bools and numbers
# -----------------

def lt.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  LLogicLogic.pj.absurdF(A, e)

def lt.eq_refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt.eq_refl(p)

def lt.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      lt.absurd({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      lt.absurd({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      %lt.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def lt.beq_true(a: Bool, b: Bool, h: {Lease.lt_beq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      lt.absurd({True{} == False{} : Bool}, h)
    case False{} True{}:
      lt.absurd({False{} == True{} : Bool}, h)
    case False{} False{}:
      {==}

def lt.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def lt.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      lt.absurd({b == True{} : Bool}, h)

def lt.or_l(a: Bool, -b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      lt.absurd({Bool.or(False{}, b) == True{} : Bool}, h)

def lt.or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def lt.or_cases(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}) -> Or({a == True{} : Bool}, {b == True{} : Bool}):
  match a:
    case True{}:
      Inl{{==}}
    case False{}:
      Inr{h}

def lt.not_true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      lt.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def lt.or_elim(-A: Type, -B: Type, -C: Type, o: Or(A, B), f: A -> C, g: B -> C) -> C:
  match o:
    case Inl{a}:
      f(a)
    case Inr{b}:
      g(b)

# Waiters and In
# --------------

def lt.weq_refl(w: Ls.Waiter) -> {True{} == Lease.lt_weq(w, w) : Bool}:
  match w:
    case Ls.Waiter{+k, +o, l}:
      match l:
        case True{}:
          %lt.eq_refl(k) : {True{} == Bool.and(_, Bool.and(Nat.is_eq(o, o), Lease.lt_beq(True{}, True{}))) : Bool}
          %lt.eq_refl(o) : {True{} == Bool.and(_, True{}) : Bool}
          {==}
        case False{}:
          %lt.eq_refl(k) : {True{} == Bool.and(_, Bool.and(Nat.is_eq(o, o), Lease.lt_beq(False{}, False{}))) : Bool}
          %lt.eq_refl(o) : {True{} == Bool.and(_, True{}) : Bool}
          {==}

def lt.weq_sound(x: Ls.Waiter, w: Ls.Waiter, +h: {Lease.lt_weq(x, w) == True{} : Bool}) -> {x == w : Ls.Waiter}:
  match x w:
    case Ls.Waiter{+k, +o, +l} Ls.Waiter{+j, +p, +m}:
      +ek = lt.eq_true(k, j, lt.and_l(Nat.is_eq(k, j), Bool.and(Nat.is_eq(o, p), Lease.lt_beq(l, m)), h))
      +hr = lt.and_r(Nat.is_eq(k, j), Bool.and(Nat.is_eq(o, p), Lease.lt_beq(l, m)), h)
      +eo = lt.eq_true(o, p, lt.and_l(Nat.is_eq(o, p), Lease.lt_beq(l, m), hr))
      +el = lt.beq_true(l, m, lt.and_r(Nat.is_eq(o, p), Lease.lt_beq(l, m), hr))
      %ek : {Ls.Waiter{k, o, l} == Ls.Waiter{_, p, m} : Ls.Waiter}
      %eo : {Ls.Waiter{k, o, l} == Ls.Waiter{k, _, m} : Ls.Waiter}
      %el : {Ls.Waiter{k, o, l} == Ls.Waiter{k, o, _} : Ls.Waiter}
      {==}

def lt.in_sound(+x: Ls.Waiter, q: List<&2, Ls.Waiter>, i: Ls.In(x, q)) -> {Lease.lt_in(x, q) == True{} : Bool}:
  match q:
    case Nil{}:
      Empty.absurd({Lease.lt_in(x, Nil{}) == True{} : Bool}, i)
    case +w <> t:
      match i:
        case Inl{eq}:
          %Equal.sym(Ls.Waiter, x, w, eq) : {Bool.or(Lease.lt_weq(_, w), Lease.lt_in(x, t)) == True{} : Bool}
          %lt.weq_refl(w) : {Bool.or(_, Lease.lt_in(x, t)) == True{} : Bool}
          {==}
        case Inr{it}:
          lt.or_r(Lease.lt_weq(x, w), Lease.lt_in(x, t), lt.in_sound(x, t, it))

def lt.in_complete(+x: Ls.Waiter, q: List<&2, Ls.Waiter>, h: {Lease.lt_in(x, q) == True{} : Bool}) -> Ls.In(x, q):
  match q:
    case Nil{}:
      lt.absurd(Ls.In(x, Nil{}), h)
    case +w <> t:
      lt.or_elim({Lease.lt_weq(x, w) == True{} : Bool}, {Lease.lt_in(x, t) == True{} : Bool}, Ls.In(x, w <> t), lt.or_cases(Lease.lt_weq(x, w), Lease.lt_in(x, t), h), e => Inl{lt.weq_sound(x, w, e)}, r => Inr{lt.in_complete(x, t, r)})

# Kept
# ----

def lt.holds_refl(+k: Nat, +o: Nat) -> {True{} == Lease.lt_holds(Some{Ls.Lease{k, o}}, k, o) : Bool}:
  %lt.eq_refl(k) : {True{} == Bool.and(_, Nat.is_eq(o, o)) : Bool}
  lt.eq_refl(o)

def lt.holds_sound(h: Maybe<&2, Ls.Lease>, +k: Nat, +o: Nat, +e: {Lease.lt_holds(h, k, o) == True{} : Bool}) -> {h == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}:
  match h:
    case None{}:
      lt.absurd({None{} == Some{Ls.Lease{k, o}} : Maybe<&2, Ls.Lease>}, e)
    case Some{x}:
      match x:
        case Ls.Lease{+hk, +ho}:
          +ek = lt.eq_true(hk, k, lt.and_l(Nat.is_eq(hk, k), Nat.is_eq(ho, o), e))
          +eo = lt.eq_true(ho, o, lt.and_r(Nat.is_eq(hk, k), Nat.is_eq(ho, o), e))
          %ek : {Some{Ls.Lease{hk, ho}} == Some{Ls.Lease{_, o}} : Maybe<&2, Ls.Lease>}
          %eo : {Some{Ls.Lease{hk, ho}} == Some{Ls.Lease{hk, _}} : Maybe<&2, Ls.Lease>}
          {==}

def lt.kept_sound(+k: Nat, +o: Nat, s: Ls.L, kp: Ls.Kept(k, o, s)) -> {Lease.lt_kept(k, o, s) == True{} : Bool}:
  match s:
    case Ls.L{n, h, +q}:
      match kp:
        case Inl{e}:
          %Equal.sym(Maybe<&2, Ls.Lease>, h, Some{Ls.Lease{k, o}}, e) : {Bool.or(Lease.lt_holds(_, k, o), Lease.lt_in(Ls.Waiter{k, o, True{}}, q)) == True{} : Bool}
          %lt.holds_refl(k, o) : {Bool.or(_, Lease.lt_in(Ls.Waiter{k, o, True{}}, q)) == True{} : Bool}
          {==}
        case Inr{i}:
          lt.or_r(Lease.lt_holds(h, k, o), Lease.lt_in(Ls.Waiter{k, o, True{}}, q), lt.in_sound(Ls.Waiter{k, o, True{}}, q, i))

def lt.kept_complete(+k: Nat, +o: Nat, s: Ls.L, c: {Lease.lt_kept(k, o, s) == True{} : Bool}) -> Ls.Kept(k, o, s):
  match s:
    case Ls.L{n, +h, +q}:
      lt.or_elim({Lease.lt_holds(h, k, o) == True{} : Bool}, {Lease.lt_in(Ls.Waiter{k, o, True{}}, q) == True{} : Bool}, Ls.Kept(k, o, Ls.L{n, h, q}), lt.or_cases(Lease.lt_holds(h, k, o), Lease.lt_in(Ls.Waiter{k, o, True{}}, q), c), e => Inl{lt.holds_sound(h, k, o, e)}, r => Inr{lt.in_complete(Ls.Waiter{k, o, True{}}, q, r)})

# Fifo
# ----

def lt.asc_sound(q: List<&2, Ls.Waiter>, lo: Maybe<&2, Nat>, a: Ls.Asc(lo, q)) -> {Lease.lt_asc(q, lo) == True{} : Bool}:
  match q:
    case Nil{}:
      {==}
    case w <> t:
      match w:
        case Ls.Waiter{+k, o, l}:
          match lo:
            case None{}:
              (g, r) = a
              lt.asc_sound(t, Some{k}, r)
            case Some{b}:
              (g, r) = a
              %Equal.sym(Bool, Nat.is_lt(b, k), True{}, g) : {Bool.and(_, Lease.lt_asc(t, Some{k})) == True{} : Bool}
              lt.asc_sound(t, Some{k}, r)

def lt.asc_complete(q: List<&2, Ls.Waiter>, lo: Maybe<&2, Nat>, +h: {Lease.lt_asc(q, lo) == True{} : Bool}) -> Ls.Asc(lo, q):
  match q:
    case Nil{}:
      Unit{}
    case w <> t:
      match w:
        case Ls.Waiter{+k, o, l}:
          match lo:
            case None{}:
              ({==}, lt.asc_complete(t, Some{k}, h))
            case Some{+b}:
              (lt.and_l(Nat.is_lt(b, k), Lease.lt_asc(t, Some{k}), h), lt.asc_complete(t, Some{k}, lt.and_r(Nat.is_lt(b, k), Lease.lt_asc(t, Some{k}), h)))

def lt.fifo_sound(s: Ls.L, f: Ls.Fifo(s)) -> {Lease.lt_fifo(s) == True{} : Bool}:
  match s:
    case Ls.L{n, h, q}:
      match h:
        case None{}:
          lt.asc_sound(q, None{}, f)
        case Some{x}:
          match x:
            case Ls.Lease{hk, ho}:
              lt.asc_sound(q, Some{hk}, f)

def lt.fifo_complete(s: Ls.L, c: {Lease.lt_fifo(s) == True{} : Bool}) -> Ls.Fifo(s):
  match s:
    case Ls.L{n, h, q}:
      match h:
        case None{}:
          lt.asc_complete(q, None{}, c)
        case Some{x}:
          match x:
            case Ls.Lease{hk, ho}:
              lt.asc_complete(q, Some{hk}, c)

# Busy
# ----

def lt.dead_sound(q: List<&2, Ls.Waiter>, d: Ls.Dead(q)) -> {Lease.lt_dead(q) == True{} : Bool}:
  match q:
    case Nil{}:
      {==}
    case w <> t:
      match w:
        case Ls.Waiter{k, o, l}:
          (dl, dt) = d
          %Equal.sym(Bool, l, False{}, dl) : {Bool.and(Bool.not(_), Lease.lt_dead(t)) == True{} : Bool}
          lt.dead_sound(t, dt)

def lt.dead_complete(q: List<&2, Ls.Waiter>, h: {Lease.lt_dead(q) == True{} : Bool}) -> Ls.Dead(q):
  match q:
    case Nil{}:
      Unit{}
    case w <> t:
      match w:
        case Ls.Waiter{k, o, l}:
          match l:
            case True{}:
              lt.absurd(Ls.Dead(Ls.Waiter{k, o, True{}} <> t), h)
            case False{}:
              ({==}, lt.dead_complete(t, h))

def lt.busy_sound(s: Ls.L, b: Ls.Busy(s)) -> {Lease.lt_busy(s) == True{} : Bool}:
  match s:
    case Ls.L{n, h, q}:
      match h:
        case None{}:
          lt.dead_sound(q, b)
        case Some{x}:
          {==}

def lt.busy_complete(s: Ls.L, c: {Lease.lt_busy(s) == True{} : Bool}) -> Ls.Busy(s):
  match s:
    case Ls.L{n, h, q}:
      match h:
        case None{}:
          lt.dead_complete(q, c)
        case Some{x}:
          Unit{}

# NotHeld
# -------

def lt.nh_sound(+hk: Nat, +k: Nat, b: Bool, e: {Nat.is_eq(hk, k) == b : Bool}, nh: {hk == k : Nat} -> Empty) -> {Bool.not(Nat.is_eq(hk, k)) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.not(Nat.is_eq(hk, k)) == True{} : Bool}, nh(lt.eq_true(hk, k, e)))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(hk, k), False{}, e) : {Bool.not(_) == True{} : Bool}
      {==}

def lt.notheld_sound(+k: Nat, h: Maybe<&2, Ls.Lease>, nh: Ls.NotHeld(k, h)) -> {Lease.lt_notheld(k, h) == True{} : Bool}:
  match h:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Ls.Lease{+hk, ho}:
          lt.nh_sound(hk, k, Nat.is_eq(hk, k), {==}, nh)

def lt.nh_clash(+hk: Nat, +k: Nat, c: {Bool.not(Nat.is_eq(hk, k)) == True{} : Bool}, eq: {hk == k : Nat}) -> Empty:
  +same = Equal.cong(Nat, Bool, v => Bool.not(Nat.is_eq(v, k)), hk, k, eq)
  +refl = Equal.cong(Bool, Bool, v => Bool.not(v), True{}, Nat.is_eq(k, k), lt.eq_refl(k))
  lt.absurd(Empty, Equal.trans(Bool, False{}, Bool.not(Nat.is_eq(k, k)), True{}, refl, Equal.trans(Bool, Bool.not(Nat.is_eq(k, k)), Bool.not(Nat.is_eq(hk, k)), True{}, Equal.sym(Bool, Bool.not(Nat.is_eq(hk, k)), Bool.not(Nat.is_eq(k, k)), same), c)))

def lt.notheld_complete(+k: Nat, h: Maybe<&2, Ls.Lease>, c: {Lease.lt_notheld(k, h) == True{} : Bool}) -> Ls.NotHeld(k, h):
  match h:
    case None{}:
      Unit{}
    case Some{x}:
      match x:
        case Ls.Lease{+hk, ho}:
          eq => lt.nh_clash(hk, k, c, eq)

# Freed
# -----

def lt.nonefrom_sound(+o: Nat, q: List<&2, Ls.Waiter>, nf: Ls.NoneFrom(o, q)) -> {Lease.lt_nonefrom(o, q) == True{} : Bool}:
  match q:
    case Nil{}:
      {==}
    case w <> t:
      match w:
        case Ls.Waiter{k, wo, l}:
          (e, r) = nf
          %Equal.sym(Bool, Nat.is_eq(wo, o), False{}, e) : {Bool.and(Bool.not(_), Lease.lt_nonefrom(o, t)) == True{} : Bool}
          lt.nonefrom_sound(o, t, r)

def lt.nonefrom_complete(+o: Nat, q: List<&2, Ls.Waiter>, +h: {Lease.lt_nonefrom(o, q) == True{} : Bool}) -> Ls.NoneFrom(o, q):
  match q:
    case Nil{}:
      Unit{}
    case w <> t:
      match w:
        case Ls.Waiter{k, +wo, l}:
          (lt.not_true(Nat.is_eq(wo, o), lt.and_l(Bool.not(Nat.is_eq(wo, o)), Lease.lt_nonefrom(o, t), h)), lt.nonefrom_complete(o, t, lt.and_r(Bool.not(Nat.is_eq(wo, o)), Lease.lt_nonefrom(o, t), h)))

def lt.freed_sound(+o: Nat, s: Ls.L, f: Ls.Freed(o, s)) -> {Lease.lt_freed(o, s) == True{} : Bool}:
  match s:
    case Ls.L{n, h, q}:
      match h:
        case None{}:
          (nf, nq) = f
          lt.nonefrom_sound(o, q, nq)
        case Some{x}:
          match x:
            case Ls.Lease{hk, ho}:
              (nf, nq) = f
              %Equal.sym(Bool, Nat.is_eq(ho, o), False{}, nf) : {Bool.and(Bool.not(_), Lease.lt_nonefrom(o, q)) == True{} : Bool}
              lt.nonefrom_sound(o, q, nq)

def lt.freed_complete(+o: Nat, s: Ls.L, +c: {Lease.lt_freed(o, s) == True{} : Bool}) -> Ls.Freed(o, s):
  match s:
    case Ls.L{n, h, +q}:
      match h:
        case None{}:
          (Unit{}, lt.nonefrom_complete(o, q, c))
        case Some{x}:
          match x:
            case Ls.Lease{hk, +ho}:
              (lt.not_true(Nat.is_eq(ho, o), lt.and_l(Bool.not(Nat.is_eq(ho, o)), Lease.lt_nonefrom(o, q), c)), lt.nonefrom_complete(o, q, lt.and_r(Bool.not(Nat.is_eq(ho, o)), Lease.lt_nonefrom(o, q), c)))
