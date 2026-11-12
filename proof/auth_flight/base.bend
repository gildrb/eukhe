# eukhe: lemmas the proofs of area auth_flight share (the model: its
# invariant over the laws' runs am_run, laws/auth_flight/model.bend)

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/model.bend as AuthFlight
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat

def auth_flight.pf.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : LLogicLogic.auth_flight.pf.BD(_, A, Unit)
  Unit{}

def pf.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def pf.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, x => pf.pred(x), 1n+a, 1n+b, e)

def pf.MD(-A: Data, m: Maybe<&2, A>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

def pf.none_some(-A: Data, -B: Type, -x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> B:
  %e : pf.MD(A, _, Unit, B)
  Unit{}

def pf.some_inj(-A: Data, +d: A, -x: A, -y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, d), Some{x}, Some{y}, e)

def pf.add_succ_ne_zero(-A: Type, a: Nat, -b: Nat, e: {Nat.add(a, 1n+b) == 0n : Nat}) -> A:
  match a:
    case 0n:
      LLogicLogic.pf.succ_ne_zero(A, b, e)
    case 1n+p:
      LLogicLogic.pf.succ_ne_zero(A, Nat.add(p, 1n+b), e)

# a + (1 + b) == 1: both are 0
def pf.add_one(a: Nat, -b: Nat, e: {Nat.add(a, 1n+b) == 1n : Nat}) -> ({a == 0n : Nat} & {b == 0n : Nat}):
  match a:
    case 0n:
      ({==}, pf.succ_inj(b, 0n, e))
    case 1n+p:
      pf.add_succ_ne_zero(({1n+p == 0n : Nat} & {b == 0n : Nat}), p, b, pf.succ_inj(Nat.add(p, 1n+b), 0n, e))

def pf.add_zero_r(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pf.add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def pf.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pf.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# a <= b, by peeling both (the proofs' order; pf.le_is_le ties it to
# Nat.is_le, which the laws read)
def pf.le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n _:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      pf.le(p, q)

def pf.le_is_le(a: Nat, b: Nat) -> {pf.le(a, b) == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pf.le_is_le(p, q)

# Nat.is_le from pf.le
def pf.is_le(+a: Nat, +b: Nat, h: {pf.le(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(a, b), pf.le(a, b), True{}, Equal.sym(Bool, pf.le(a, b), Nat.is_le(a, b), pf.le_is_le(a, b)), h)

def auth_flight.pf.le_refl(n: Nat) -> {pf.le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      auth_flight.pf.le_refl(p)

def auth_flight.pf.le_succ(a: Nat, b: Nat, h: {pf.le(a, b) == True{} : Bool}) -> {pf.le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      auth_flight.pf.absurdF({pf.le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      auth_flight.pf.le_succ(p, q, h)

def pf.fst(-A: Type, -B: Type, p: (A & B)) -> A:
  (a, b) = p
  a

# Lists
# -----

def pf.drop_zero(-A: Data, xs: List<&2, A>) -> {xs == List.drop(&2, A, xs, 0n) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def pf.get_snoc(-A: Data, xs: List<&2, A>, +x: A) -> {List.get(&2, A, List.append(&2, A, xs, [x]), List.length(&2, A, xs)) == Some{x} : Maybe<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      pf.get_snoc(A, t, x)

def pf.get_append(-A: Data, xs: List<&2, A>, k: Nat, -x: A, +ys: List<&2, A>, g: {List.get(&2, A, xs, k) == Some{x} : Maybe<&2, A>}) -> {List.get(&2, A, List.append(&2, A, xs, ys), k) == Some{x} : Maybe<&2, A>}:
  match xs k:
    case Nil{} _:
      pf.none_some(A, {List.get(&2, A, ys, k) == Some{x} : Maybe<&2, A>}, x, g)
    case h <> t 0n:
      g
    case h <> t 1n+p:
      pf.get_append(A, t, p, x, ys, g)

# a list is the items before k, item k, and the items after it
def pf.split(-A: Data, +d: A, xs: List<&2, A>, k: Nat, -x: A, g: {List.get(&2, A, xs, k) == Some{x} : Maybe<&2, A>}) -> {xs == List.append(&2, A, List.take(&2, A, xs, k), x <> List.drop(&2, A, xs, 1n+k)) : List<&2, A>}:
  match xs k:
    case Nil{} _:
      pf.none_some(A, {Nil{} == List.append(&2, A, List.take(&2, A, Nil{}, k), x <> List.drop(&2, A, Nil{}, 1n+k)) : List<&2, A>}, x, g)
    case +h <> +t 0n:
      %pf.some_inj(A, d, h, x, g) : {h <> t == _ <> List.drop(&2, A, t, 0n) : List<&2, A>}
      %pf.drop_zero(A, t) : {h <> t == h <> _ : List<&2, A>}
      {==}
    case +h <> +t 1n+p:
      %pf.split(A, d, t, p, x, g) : {h <> t == h <> _ : List<&2, A>}
      {==}

# item k of the list with item k replaced is the new item
def pf.get_put(-A: Data, xs: List<&2, A>, k: Nat, -x: A, +y: A, g: {List.get(&2, A, xs, k) == Some{x} : Maybe<&2, A>}) -> {List.get(&2, A, List.append(&2, A, List.take(&2, A, xs, k), y <> List.drop(&2, A, xs, 1n+k)), k) == Some{y} : Maybe<&2, A>}:
  match xs k:
    case Nil{} _:
      pf.none_some(A, {List.get(&2, A, List.append(&2, A, List.take(&2, A, Nil{}, k), y <> List.drop(&2, A, Nil{}, 1n+k)), k) == Some{y} : Maybe<&2, A>}, x, g)
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      pf.get_put(A, t, p, x, y, g)

# The invariant
# -------------

# 1 for a caller that leads a flight
def pf.lead(l: F.Leg) -> Nat:
  match l:
    case F.Load{}:
      0n
    case F.Board{}:
      0n
    case F.Check{f}:
      1n
    case F.Fetch{f}:
      1n
    case F.Store{f, c}:
      1n
    case F.Land{f, o}:
      1n
    case F.Waiting{f}:
      0n
    case F.Served{v, o}:
      0n

# the callers that lead a flight
def pf.leads(cs: List<&2, F.Leg>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case l <> t:
      Nat.add(pf.lead(l), pf.leads(t))

# the flights in flight
def pf.holds(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# a leader leads the flight in flight, the one that lands next
def pf.Lead(+fl: Bool, +ld: List<&2, F.Out>, f: Nat) -> Type:
  ({fl == True{} : Bool} & {f == List.length(&2, F.Out, ld) : Nat})

# a credential about to land is stored, or a newer one
def pf.Kept(o: F.Out, +s: F.Sto) -> Type:
  match o:
    case F.Ok{c}:
      {pf.le(c, F.Sto.c(s)) == True{} : Bool}
    case F.Err{e}:
      Unit

# a finished caller of flight f holds f's outcome
def pf.Got(+ld: List<&2, F.Out>, v: Maybe<&2, Nat>, o: F.Out) -> Type:
  match v:
    case None{}:
      Unit
    case Some{f}:
      {List.get(&2, F.Out, ld, f) == Some{o} : Maybe<&2, F.Out>}

# a caller waiting on flight f: f landed (m, its outcome, is some), or f
# is the flight in flight
def pf.WtM(m: Maybe<&2, F.Out>, +fl: Bool, +ld: List<&2, F.Out>, f: Nat) -> Type:
  match m:
    case None{}:
      pf.Lead(fl, ld, f)
    case Some{o}:
      Unit

def pf.Wt(+fl: Bool, +ld: List<&2, F.Out>, +f: Nat) -> Type:
  pf.WtM(List.get(&2, F.Out, ld, f), fl, ld, f)

def pf.Good(w: F.W, l: F.Leg) -> Type:
  match w:
    case F.W{+s, +fl, +ld, n}:
      match l:
        case F.Load{}:
          Unit
        case F.Board{}:
          Unit
        case F.Check{f}:
          pf.Lead(fl, ld, f)
        case F.Fetch{f}:
          pf.Lead(fl, ld, f)
        case F.Store{f, c}:
          pf.Lead(fl, ld, f)
        case F.Land{f, o}:
          (pf.Lead(fl, ld, f) & pf.Kept(o, s))
        case F.Waiting{+f}:
          pf.Wt(fl, ld, f)
        case F.Served{v, o}:
          pf.Got(ld, v, o)

def pf.All(+w: F.W, cs: List<&2, F.Leg>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case l <> t:
      (pf.Good(w, l) & pf.All(w, t))

def auth_flight.pf.Inv(s: F.St) -> Type:
  match s:
    case F.St{+w, +cs}:
      ({pf.leads(cs) == pf.holds(F.W.fl(w)) : Nat} & pf.All(w, cs))

# Counting and splitting the callers
# ----------------------------------

def pf.leads_append(xs: List<&2, F.Leg>, +ys: List<&2, F.Leg>) -> {pf.leads(List.append(&2, F.Leg, xs, ys)) == Nat.add(pf.leads(xs), pf.leads(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Nat, Nat.add(Nat.add(pf.lead(h), pf.leads(t)), pf.leads(ys)), Nat.add(pf.lead(h), Nat.add(pf.leads(t), pf.leads(ys))), pf.add_assoc(pf.lead(h), pf.leads(t), pf.leads(ys))) : {Nat.add(pf.lead(h), pf.leads(List.append(&2, F.Leg, t, ys))) == _ : Nat}
      %pf.leads_append(t, ys) : {Nat.add(pf.lead(h), pf.leads(List.append(&2, F.Leg, t, ys))) == Nat.add(pf.lead(h), _) : Nat}
      {==}

def pf.all_split.cons(+w: F.W, -h: F.Leg, -t: List<&2, F.Leg>, -l: F.Leg, -post: List<&2, F.Leg>, gh: pf.Good(w, h), r: (pf.All(w, t) & (pf.Good(w, l) & pf.All(w, post)))) -> (pf.All(w, h <> t) & (pf.Good(w, l) & pf.All(w, post))):
  (ap, rest) = r
  ((gh, ap), rest)

def pf.all_split(+w: F.W, pre: List<&2, F.Leg>, -l: F.Leg, -post: List<&2, F.Leg>, a: pf.All(w, List.append(&2, F.Leg, pre, l <> post))) -> (pf.All(w, pre) & (pf.Good(w, l) & pf.All(w, post))):
  match pre:
    case Nil{}:
      (Unit{}, a)
    case h <> t:
      (gh, at) = a
      pf.all_split.cons(w, h, t, l, post, gh, pf.all_split(w, t, l, post, at))

def pf.all_join(+w: F.W, pre: List<&2, F.Leg>, -l: F.Leg, -post: List<&2, F.Leg>, ap: pf.All(w, pre), gl: pf.Good(w, l), aq: pf.All(w, post)) -> pf.All(w, List.append(&2, F.Leg, pre, l <> post)):
  match pre:
    case Nil{}:
      (gl, aq)
    case h <> t:
      (gh, at) = ap
      (gh, pf.all_join(w, t, l, post, at, gl, aq))

def pf.all_get(+w: F.W, cs: List<&2, F.Leg>, k: Nat, -x: F.Leg, g: {List.get(&2, F.Leg, cs, k) == Some{x} : Maybe<&2, F.Leg>}, a: pf.All(w, cs)) -> pf.Good(w, x):
  match cs k:
    case Nil{} _:
      pf.none_some(F.Leg, pf.Good(w, x), x, g)
    case +h <> t 0n:
      (gh, at) = a
      %pf.some_inj(F.Leg, F.Load{}, h, x, g) : pf.Good(w, _)
      gh
    case h <> t 1n+p:
      (gh, at) = a
      pf.all_get(w, t, p, x, g, at)

# the invariant of a world and callers that are one list split at a leg
def pf.inv_of(+w: F.W, +pre: List<&2, F.Leg>, +l: F.Leg, +post: List<&2, F.Leg>, n: {Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))) == pf.holds(F.W.fl(w)) : Nat}, ap: pf.All(w, pre), gl: pf.Good(w, l), aq: pf.All(w, post)) -> auth_flight.pf.Inv(F.St{w, List.append(&2, F.Leg, pre, l <> post)}):
  (Equal.trans(Nat, pf.leads(List.append(&2, F.Leg, pre, l <> post)), Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))), pf.holds(F.W.fl(w)), pf.leads_append(pre, l <> post), n), pf.all_join(w, pre, l, post, ap, gl, aq))

# Frames: what a step leaves of the other callers
# ------------------------------------------------

# a waiter's flight landed or is in flight: a flight starting keeps it
# (no flight was in flight, so its flight landed)
def pf.wt_flon(m: Maybe<&2, F.Out>, +ld: List<&2, F.Out>, +f: Nat, g: pf.WtM(m, False{}, ld, f)) -> pf.WtM(m, True{}, ld, f):
  match m:
    case None{}:
      (e, _) = g
      auth_flight.pf.absurdF(pf.Lead(True{}, ld, f), e)
    case Some{o}:
      Unit{}

# a waiter's flight landed or is in flight: a land keeps it landed (an
# outcome once landed stays), or lands it (the flight in flight is the
# one that lands, at index |ld|)
def pf.wt_land(m: Maybe<&2, F.Out>, +fl: Bool, +ld: List<&2, F.Out>, +o: F.Out, +f: Nat, e: {List.get(&2, F.Out, ld, f) == m : Maybe<&2, F.Out>}, g: pf.WtM(m, fl, ld, f)) -> pf.Wt(False{}, List.append(&2, F.Out, ld, [o]), f):
  match m:
    case None{}:
      (efl, ef) = g
      %Equal.sym(Nat, f, List.length(&2, F.Out, ld), ef) : pf.Wt(False{}, List.append(&2, F.Out, ld, [o]), _)
      %Equal.sym(Maybe<&2, F.Out>, List.get(&2, F.Out, List.append(&2, F.Out, ld, [o]), List.length(&2, F.Out, ld)), Some{o}, pf.get_snoc(F.Out, ld, o)) : pf.WtM(_, False{}, List.append(&2, F.Out, ld, [o]), List.length(&2, F.Out, ld))
      Unit{}
    case Some{o2}:
      %Equal.sym(Maybe<&2, F.Out>, List.get(&2, F.Out, List.append(&2, F.Out, ld, [o]), f), Some{o2}, pf.get_append(F.Out, ld, f, o2, [o], e)) : pf.WtM(_, False{}, List.append(&2, F.Out, ld, [o]), f)
      Unit{}

# a flight starts: no leader was in flight
def pf.good_flon(+s: F.Sto, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, g: pf.Good(F.W{s, False{}, ld, n}, l)) -> pf.Good(F.W{s, True{}, ld, n}, l):
  match l:
    case F.Load{}:
      Unit{}
    case F.Board{}:
      Unit{}
    case F.Check{f}:
      (e, _) = g
      auth_flight.pf.absurdF(pf.Lead(True{}, ld, f), e)
    case F.Fetch{f}:
      (e, _) = g
      auth_flight.pf.absurdF(pf.Lead(True{}, ld, f), e)
    case F.Store{f, c}:
      (e, _) = g
      auth_flight.pf.absurdF(pf.Lead(True{}, ld, f), e)
    case F.Land{f, o}:
      (lead, _) = g
      (e, _) = lead
      auth_flight.pf.absurdF((pf.Lead(True{}, ld, f) & pf.Kept(o, s)), e)
    case F.Waiting{+f}:
      pf.wt_flon(List.get(&2, F.Out, ld, f), ld, f, g)
    case F.Served{v, o}:
      g

def pf.all_flon(+s: F.Sto, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, a: pf.All(F.W{s, False{}, ld, n}, cs)) -> pf.All(F.W{s, True{}, ld, n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case h <> t:
      (gh, at) = a
      (pf.good_flon(s, ld, n, h, gh), pf.all_flon(s, ld, n, t, at))

# a fetch counts: no leg depends on the count
def pf.good_fetch(+s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, g: pf.Good(F.W{s, fl, ld, n}, l)) -> pf.Good(F.W{s, fl, ld, 1n+n}, l):
  match l:
    case F.Load{}:
      g
    case F.Board{}:
      g
    case F.Check{f}:
      g
    case F.Fetch{f}:
      g
    case F.Store{f, c}:
      g
    case F.Land{f, o}:
      g
    case F.Waiting{f}:
      g
    case F.Served{v, o}:
      g

def pf.all_fetch(+s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, a: pf.All(F.W{s, fl, ld, n}, cs)) -> pf.All(F.W{s, fl, ld, 1n+n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case h <> t:
      (gh, at) = a
      (pf.good_fetch(s, fl, ld, n, h, gh), pf.all_fetch(s, fl, ld, n, t, at))

# the leader stores: no other caller leads
def pf.good_store(+s1: F.Sto, +s2: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, z: {pf.lead(l) == 0n : Nat}, g: pf.Good(F.W{s1, fl, ld, n}, l)) -> pf.Good(F.W{s2, fl, ld, n}, l):
  match l:
    case F.Load{}:
      Unit{}
    case F.Board{}:
      Unit{}
    case F.Check{f}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(fl, ld, f), 0n, z)
    case F.Fetch{f}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(fl, ld, f), 0n, z)
    case F.Store{f, c}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(fl, ld, f), 0n, z)
    case F.Land{f, o}:
      LLogicLogic.pf.succ_ne_zero((pf.Lead(fl, ld, f) & pf.Kept(o, s2)), 0n, z)
    case F.Waiting{f}:
      g
    case F.Served{v, o}:
      g

def pf.all_store(+s1: F.Sto, +s2: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, +z: {pf.leads(cs) == 0n : Nat}, a: pf.All(F.W{s1, fl, ld, n}, cs)) -> pf.All(F.W{s2, fl, ld, n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case +h <> +t:
      (gh, at) = a
      (pf.good_store(s1, s2, fl, ld, n, h, pf.fst({pf.lead(h) == 0n : Nat}, {pf.leads(t) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.lead(h), pf.leads(t), z)), gh), pf.all_store(s1, s2, fl, ld, n, t, LLogicLogic.pf.snd({pf.lead(h) == 0n : Nat}, {pf.leads(t) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.lead(h), pf.leads(t), z)), at))

# the leader lands: no other caller leads, and the landed outcomes only grow
def pf.got_land(+ld: List<&2, F.Out>, +o: F.Out, v: Maybe<&2, Nat>, +o2: F.Out, g: pf.Got(ld, v, o2)) -> pf.Got(List.append(&2, F.Out, ld, [o]), v, o2):
  match v:
    case None{}:
      Unit{}
    case Some{f}:
      pf.get_append(F.Out, ld, f, o2, [o], g)

def pf.good_land(+s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +o: F.Out, +n: Nat, l: F.Leg, z: {pf.lead(l) == 0n : Nat}, g: pf.Good(F.W{s, fl, ld, n}, l)) -> pf.Good(F.W{s, False{}, List.append(&2, F.Out, ld, [o]), n}, l):
  match l:
    case F.Load{}:
      Unit{}
    case F.Board{}:
      Unit{}
    case F.Check{f}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(False{}, List.append(&2, F.Out, ld, [o]), f), 0n, z)
    case F.Fetch{f}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(False{}, List.append(&2, F.Out, ld, [o]), f), 0n, z)
    case F.Store{f, c}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(False{}, List.append(&2, F.Out, ld, [o]), f), 0n, z)
    case F.Land{f, o3}:
      LLogicLogic.pf.succ_ne_zero((pf.Lead(False{}, List.append(&2, F.Out, ld, [o]), f) & pf.Kept(o3, s)), 0n, z)
    case F.Waiting{+f}:
      pf.wt_land(List.get(&2, F.Out, ld, f), fl, ld, o, f, {==}, g)
    case F.Served{v, o2}:
      pf.got_land(ld, o, v, o2, g)

def pf.all_land(+s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +o: F.Out, +n: Nat, cs: List<&2, F.Leg>, +z: {pf.leads(cs) == 0n : Nat}, a: pf.All(F.W{s, fl, ld, n}, cs)) -> pf.All(F.W{s, False{}, List.append(&2, F.Out, ld, [o]), n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case +h <> +t:
      (gh, at) = a
      (pf.good_land(s, fl, ld, o, n, h, pf.fst({pf.lead(h) == 0n : Nat}, {pf.leads(t) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.lead(h), pf.leads(t), z)), gh), pf.all_land(s, fl, ld, o, n, t, LLogicLogic.pf.snd({pf.lead(h) == 0n : Nat}, {pf.leads(t) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.lead(h), pf.leads(t), z)), at))

# a peer stores a newer credential
def pf.kept_peer(o: F.Out, +c: Nat, +fr: Bool, k: pf.Kept(o, F.Sto{c, fr})) -> pf.Kept(o, F.Sto{1n+c, True{}}):
  match o:
    case F.Ok{c2}:
      auth_flight.pf.le_succ(c2, c, k)
    case F.Err{e}:
      Unit{}

def pf.good_peer(+c: Nat, +fr: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, g: pf.Good(F.W{F.Sto{c, fr}, fl, ld, n}, l)) -> pf.Good(F.W{F.Sto{1n+c, True{}}, fl, ld, n}, l):
  match l:
    case F.Load{}:
      Unit{}
    case F.Board{}:
      Unit{}
    case F.Check{f}:
      g
    case F.Fetch{f}:
      g
    case F.Store{f, c2}:
      g
    case F.Land{f, o}:
      (lead, k) = g
      (lead, pf.kept_peer(o, c, fr, k))
    case F.Waiting{f}:
      g
    case F.Served{v, o}:
      g

def pf.all_peer(+c: Nat, +fr: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, a: pf.All(F.W{F.Sto{c, fr}, fl, ld, n}, cs)) -> pf.All(F.W{F.Sto{1n+c, True{}}, fl, ld, n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case h <> t:
      (gh, at) = a
      (pf.good_peer(c, fr, fl, ld, n, h, gh), pf.all_peer(c, fr, fl, ld, n, t, at))

# the stored credential expires: it stays the stored one
def pf.kept_expire(o: F.Out, +c: Nat, +fr: Bool, k: pf.Kept(o, F.Sto{c, fr})) -> pf.Kept(o, F.Sto{c, False{}}):
  match o:
    case F.Ok{c2}:
      k
    case F.Err{e}:
      Unit{}

def pf.good_expire(+c: Nat, +fr: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, g: pf.Good(F.W{F.Sto{c, fr}, fl, ld, n}, l)) -> pf.Good(F.W{F.Sto{c, False{}}, fl, ld, n}, l):
  match l:
    case F.Load{}:
      Unit{}
    case F.Board{}:
      Unit{}
    case F.Check{f}:
      g
    case F.Fetch{f}:
      g
    case F.Store{f, c2}:
      g
    case F.Land{f, o}:
      (lead, k) = g
      (lead, pf.kept_expire(o, c, fr, k))
    case F.Waiting{f}:
      g
    case F.Served{v, o}:
      g

def pf.all_expire(+c: Nat, +fr: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, a: pf.All(F.W{F.Sto{c, fr}, fl, ld, n}, cs)) -> pf.All(F.W{F.Sto{c, False{}}, fl, ld, n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case h <> t:
      (gh, at) = a
      (pf.good_expire(c, fr, fl, ld, n, h, gh), pf.all_expire(c, fr, fl, ld, n, t, at))

# A step keeps the invariant
# --------------------------

def pf.zero_sum(-a: Nat, -b: Nat, za: {a == 0n : Nat}, zb: {b == 0n : Nat}) -> {Nat.add(a, b) == 0n : Nat}:
  %Equal.sym(Nat, a, 0n, za) : {Nat.add(_, b) == 0n : Nat}
  zb

def pf.core.start.count(-a: Nat, -b: Nat, za: {a == 0n : Nat}, zb: {b == 0n : Nat}) -> {Nat.add(a, 1n+b) == 1n : Nat}:
  %Equal.sym(Nat, a, 0n, za) : {Nat.add(_, 1n+b) == 1n : Nat}
  %Equal.sym(Nat, b, 0n, zb) : {1n+_ == 1n : Nat}
  {==}

# a caller boards and no flight is in flight: it starts the next flight
def pf.core.start(+s: F.Sto, +ld: List<&2, F.Out>, +n: Nat, +pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, +i: {Nat.add(pf.leads(pre), pf.leads(post)) == 0n : Nat}, ap: pf.All(F.W{s, False{}, ld, n}, pre), aq: pf.All(F.W{s, False{}, ld, n}, post)) -> auth_flight.pf.Inv(F.St{F.W{s, True{}, ld, n}, List.append(&2, F.Leg, pre, F.Check{List.length(&2, F.Out, ld)} <> post)}):
  +zp = pf.fst({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.leads(pre), pf.leads(post), i))
  +zq = LLogicLogic.pf.snd({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.leads(pre), pf.leads(post), i))
  pf.inv_of(F.W{s, True{}, ld, n}, pre, F.Check{List.length(&2, F.Out, ld)}, post, pf.core.start.count(pf.leads(pre), pf.leads(post), zp, zq), pf.all_flon(s, ld, n, pre, ap), ({==}, {==}), pf.all_flon(s, ld, n, post, aq))

def pf.core.land.got(-f: Nat, +ld: List<&2, F.Out>, +o: F.Out, ef: {f == List.length(&2, F.Out, ld) : Nat}) -> {List.get(&2, F.Out, List.append(&2, F.Out, ld, [o]), f) == Some{o} : Maybe<&2, F.Out>}:
  %Equal.sym(Nat, f, List.length(&2, F.Out, ld), ef) : {List.get(&2, F.Out, List.append(&2, F.Out, ld, [o]), _) == Some{o} : Maybe<&2, F.Out>}
  pf.get_snoc(F.Out, ld, o)

# the leader stores the fetched credential: no other caller leads
def pf.core.store(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, +f: Nat, +c: Nat, +x: Nat, fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +i: {Nat.add(pf.leads(pre), 1n+pf.leads(post)) == pf.holds(fl) : Nat}, ap: pf.All(F.W{F.Sto{x, False{}}, fl, ld, n}, pre), gl: pf.Lead(fl, ld, f), aq: pf.All(F.W{F.Sto{x, False{}}, fl, ld, n}, post)) -> auth_flight.pf.Inv(F.St{F.W{F.Sto{c, True{}}, fl, ld, n}, List.append(&2, F.Leg, pre, F.Land{f, F.Ok{c}} <> post)}):
  match fl:
    case True{}:
      +zp = pf.fst({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, pf.add_one(pf.leads(pre), pf.leads(post), i))
      +zq = LLogicLogic.pf.snd({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, pf.add_one(pf.leads(pre), pf.leads(post), i))
      pf.inv_of(F.W{F.Sto{c, True{}}, True{}, ld, n}, pre, F.Land{f, F.Ok{c}}, post, i, pf.all_store(F.Sto{x, False{}}, F.Sto{c, True{}}, True{}, ld, n, pre, zp, ap), (gl, auth_flight.pf.le_refl(c)), pf.all_store(F.Sto{x, False{}}, F.Sto{c, True{}}, True{}, ld, n, post, zq, aq))
    case False{}:
      (e, _) = gl
      auth_flight.pf.absurdF(auth_flight.pf.Inv(F.St{F.W{F.Sto{c, True{}}, False{}, ld, n}, List.append(&2, F.Leg, pre, F.Land{f, F.Ok{c}} <> post)}), e)

# the leader lands: no other caller leads, and no flight is in flight
def pf.core.land(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, +f: Nat, +o: F.Out, +s: F.Sto, fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +i: {Nat.add(pf.leads(pre), 1n+pf.leads(post)) == pf.holds(fl) : Nat}, ap: pf.All(F.W{s, fl, ld, n}, pre), gl: (pf.Lead(fl, ld, f) & pf.Kept(o, s)), aq: pf.All(F.W{s, fl, ld, n}, post)) -> auth_flight.pf.Inv(F.St{F.W{s, False{}, List.append(&2, F.Out, ld, [o]), n}, List.append(&2, F.Leg, pre, F.Served{Some{f}, o} <> post)}):
  match fl:
    case True{}:
      (lead, kept) = gl
      (efl, ef) = lead
      +zp = pf.fst({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, pf.add_one(pf.leads(pre), pf.leads(post), i))
      +zq = LLogicLogic.pf.snd({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, pf.add_one(pf.leads(pre), pf.leads(post), i))
      pf.inv_of(F.W{s, False{}, List.append(&2, F.Out, ld, [o]), n}, pre, F.Served{Some{f}, o}, post, pf.zero_sum(pf.leads(pre), pf.leads(post), zp, zq), pf.all_land(s, True{}, ld, o, n, pre, zp, ap), pf.core.land.got(f, ld, o, ef), pf.all_land(s, True{}, ld, o, n, post, zq, aq))
    case False{}:
      (lead, kept) = gl
      (e, _) = lead
      auth_flight.pf.absurdF(auth_flight.pf.Inv(F.St{F.W{s, False{}, List.append(&2, F.Out, ld, [o]), n}, List.append(&2, F.Leg, pre, F.Served{Some{f}, o} <> post)}), e)

# a caller that joined a flight takes its outcome once it landed; else it
# waits on, its flight still in flight (gl)
def pf.core.wait(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, +f: Nat, +s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, m: Maybe<&2, F.Out>, e: {List.get(&2, F.Out, ld, f) == m : Maybe<&2, F.Out>}, i: {Nat.add(pf.leads(pre), pf.leads(post)) == pf.holds(fl) : Nat}, ap: pf.All(F.W{s, fl, ld, n}, pre), gl: pf.Wt(fl, ld, f), aq: pf.All(F.W{s, fl, ld, n}, post)) -> auth_flight.pf.Inv(F.St{F.Adv.w(F.adv.wait.got(f, m, F.W{s, fl, ld, n})), List.append(&2, F.Leg, pre, F.Adv.l(F.adv.wait.got(f, m, F.W{s, fl, ld, n})) <> post)}):
  match m:
    case None{}:
      pf.inv_of(F.W{s, fl, ld, n}, pre, F.Waiting{f}, post, i, ap, gl, aq)
    case Some{+o}:
      pf.inv_of(F.W{s, fl, ld, n}, pre, F.Served{Some{f}, o}, post, i, ap, e, aq)

# nothing is landed at index |ld|
def pf.get_len(-A: Data, xs: List<&2, A>) -> {List.get(&2, A, xs, List.length(&2, A, xs)) == None{} : Maybe<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      pf.get_len(A, t)

# a caller that joins the flight in flight (flight |ld|, not landed)
def pf.wt_new(+ld: List<&2, F.Out>) -> pf.Wt(True{}, ld, List.length(&2, F.Out, ld)):
  %Equal.sym(Maybe<&2, F.Out>, List.get(&2, F.Out, ld, List.length(&2, F.Out, ld)), None{}, pf.get_len(F.Out, ld)) : pf.WtM(_, True{}, ld, List.length(&2, F.Out, ld))
  ({==}, {==})

# one caller's step, between the callers before it and after it
def pf.core(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, l: F.Leg, w: F.W, ok: Bool, i: {Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))) == pf.holds(F.W.fl(w)) : Nat}, ap: pf.All(w, pre), gl: pf.Good(w, l), aq: pf.All(w, post)) -> auth_flight.pf.Inv(F.St{F.Adv.w(F.adv(l, ok, w)), List.append(&2, F.Leg, pre, F.Adv.l(F.adv(l, ok, w)) <> post)}):
  match l:
    case F.Load{}:
      match w:
        case F.W{s, +fl, +ld, +n}:
          match s:
            case F.Sto{+c, fr}:
              match fr:
                case True{}:
                  pf.inv_of(F.W{F.Sto{c, True{}}, fl, ld, n}, pre, F.Served{None{}, F.Ok{c}}, post, i, ap, Unit{}, aq)
                case False{}:
                  pf.inv_of(F.W{F.Sto{c, False{}}, fl, ld, n}, pre, F.Board{}, post, i, ap, Unit{}, aq)
    case F.Board{}:
      match w:
        case F.W{+s, fl, +ld, +n}:
          match fl:
            case True{}:
              pf.inv_of(F.W{s, True{}, ld, n}, pre, F.Waiting{List.length(&2, F.Out, ld)}, post, i, ap, pf.wt_new(ld), aq)
            case False{}:
              pf.core.start(s, ld, n, pre, post, i, ap, aq)
    case F.Check{+f}:
      match w:
        case F.W{s, +fl, +ld, +n}:
          match s:
            case F.Sto{+c, fr}:
              match fr:
                case True{}:
                  pf.inv_of(F.W{F.Sto{c, True{}}, fl, ld, n}, pre, F.Land{f, F.Ok{c}}, post, i, ap, (gl, auth_flight.pf.le_refl(c)), aq)
                case False{}:
                  pf.inv_of(F.W{F.Sto{c, False{}}, fl, ld, n}, pre, F.Fetch{f}, post, i, ap, gl, aq)
    case F.Fetch{+f}:
      match w:
        case F.W{+s, +fl, +ld, +n}:
          match ok:
            case True{}:
              pf.inv_of(F.W{s, fl, ld, 1n+n}, pre, F.Store{f, 1n+n}, post, i, pf.all_fetch(s, fl, ld, n, pre, ap), gl, pf.all_fetch(s, fl, ld, n, post, aq))
            case False{}:
              pf.inv_of(F.W{s, fl, ld, 1n+n}, pre, F.Land{f, F.Err{1n+n}}, post, i, pf.all_fetch(s, fl, ld, n, pre, ap), (gl, Unit{}), pf.all_fetch(s, fl, ld, n, post, aq))
    case F.Store{+f, +c}:
      match w:
        case F.W{s, fl, +ld, +n}:
          match s:
            case F.Sto{+p, fr}:
              match fr:
                case True{}:
                  pf.inv_of(F.W{F.Sto{p, True{}}, fl, ld, n}, pre, F.Land{f, F.Ok{p}}, post, i, ap, (gl, auth_flight.pf.le_refl(p)), aq)
                case False{}:
                  pf.core.store(pre, post, f, c, p, fl, ld, n, i, ap, gl, aq)
    case F.Land{+f, +o}:
      match w:
        case F.W{+s, fl, +ld, +n}:
          pf.core.land(pre, post, f, o, s, fl, ld, n, i, ap, gl, aq)
    case F.Waiting{+f}:
      match w:
        case F.W{+s, +fl, +ld, +n}:
          pf.core.wait(pre, post, f, s, fl, ld, n, List.get(&2, F.Out, ld, f), {==}, i, ap, gl, aq)
    case F.Served{+v, +o}:
      pf.inv_of(w, pre, F.Served{v, o}, post, i, ap, gl, aq)

def pf.inv_cs(+w: F.W, -cs: List<&2, F.Leg>, -xs: List<&2, F.Leg>, e: {cs == xs : List<&2, F.Leg>}, inv: auth_flight.pf.Inv(F.St{w, cs})) -> auth_flight.pf.Inv(F.St{w, xs}):
  %e : auth_flight.pf.Inv(F.St{w, _})
  inv

def pf.inv_core.parts(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, l: F.Leg, w: F.W, ok: Bool, i: {Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))) == pf.holds(F.W.fl(w)) : Nat}, parts: (pf.All(w, pre) & (pf.Good(w, l) & pf.All(w, post)))) -> auth_flight.pf.Inv(F.St{F.Adv.w(F.adv(l, ok, w)), List.append(&2, F.Leg, pre, F.Adv.l(F.adv(l, ok, w)) <> post)}):
  (ap, rest) = parts
  (gl, aq) = rest
  pf.core(pre, post, l, w, ok, i, ap, gl, aq)

def pf.inv_core(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, +l: F.Leg, +w: F.W, ok: Bool, inv: auth_flight.pf.Inv(F.St{w, List.append(&2, F.Leg, pre, l <> post)})) -> auth_flight.pf.Inv(F.St{F.Adv.w(F.adv(l, ok, w)), List.append(&2, F.Leg, pre, F.Adv.l(F.adv(l, ok, w)) <> post)}):
  (cnt, all) = inv
  pf.inv_core.parts(pre, post, l, w, ok, Equal.trans(Nat, Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))), pf.leads(List.append(&2, F.Leg, pre, l <> post)), pf.holds(F.W.fl(w)), Equal.sym(Nat, pf.leads(List.append(&2, F.Leg, pre, l <> post)), Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))), pf.leads_append(pre, l <> post)), cnt), pf.all_split(w, pre, l, post, all))

def pf.put_eta(+k: Nat, a: F.Adv, +cs: List<&2, F.Leg>) -> {F.St{F.Adv.w(a), List.append(&2, F.Leg, List.take(&2, F.Leg, cs, k), F.Adv.l(a) <> List.drop(&2, F.Leg, cs, 1n+k))} == F.put(k, a, cs) : F.St}:
  match a:
    case F.Adv{l, w}:
      {==}

def pf.inv_at(m: Maybe<&2, F.Leg>, +k: Nat, +ok: Bool, +w: F.W, +cs: List<&2, F.Leg>, g: {List.get(&2, F.Leg, cs, k) == m : Maybe<&2, F.Leg>}, inv: auth_flight.pf.Inv(F.St{w, cs})) -> auth_flight.pf.Inv(F.step.at(m, k, ok, w, cs)):
  match m:
    case None{}:
      inv
    case Some{+l}:
      %pf.put_eta(k, F.adv(l, ok, w), cs) : auth_flight.pf.Inv(_)
      pf.inv_core(List.take(&2, F.Leg, cs, k), List.drop(&2, F.Leg, cs, 1n+k), l, w, ok, pf.inv_cs(w, cs, List.append(&2, F.Leg, List.take(&2, F.Leg, cs, k), l <> List.drop(&2, F.Leg, cs, 1n+k)), pf.split(F.Leg, F.Load{}, cs, k, l, g), inv))

def pf.inv_step(s: F.St, e: F.Ev, inv: auth_flight.pf.Inv(s)) -> auth_flight.pf.Inv(F.step(s, e)):
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fr}:
              match e:
                case F.Arrive{}:
                  (cnt, all) = inv
                  (Equal.trans(Nat, pf.leads(List.append(&2, F.Leg, cs, [F.Load{}])), pf.leads(cs), pf.holds(fl), Equal.trans(Nat, pf.leads(List.append(&2, F.Leg, cs, [F.Load{}])), Nat.add(pf.leads(cs), 0n), pf.leads(cs), pf.leads_append(cs, [F.Load{}]), pf.add_zero_r(pf.leads(cs))), cnt), pf.all_join(F.W{F.Sto{c, fr}, fl, ld, n}, cs, F.Load{}, Nil{}, all, Unit{}, Unit{}))
                case F.Step{+k, ok}:
                  pf.inv_at(List.get(&2, F.Leg, cs, k), k, ok, F.W{F.Sto{c, fr}, fl, ld, n}, cs, {==}, inv)
                case F.Peer{}:
                  (cnt, all) = inv
                  (cnt, pf.all_peer(c, fr, fl, ld, n, cs, all))
                case F.Expire{}:
                  (cnt, all) = inv
                  (cnt, pf.all_expire(c, fr, fl, ld, n, cs, all))

def pf.inv_go(evs: List<&2, F.Ev>, +s: F.St, inv: auth_flight.pf.Inv(s)) -> auth_flight.pf.Inv(AuthFlight.am_go(evs, s)):
  match evs:
    case Nil{}:
      inv
    case +e <> rest:
      pf.inv_go(rest, F.step(s, e), pf.inv_step(s, e, inv))

def pf.inv_run(evs: List<&2, F.Ev>) -> auth_flight.pf.Inv(AuthFlight.am_run(evs)):
  pf.inv_go(evs, F.St{F.W{F.Sto{0n, False{}}, False{}, Nil{}, 0n}, Nil{}}, ({==}, Unit{}))

def pf.stored(s: F.St, inv: auth_flight.pf.Inv(s), +k: Nat, +f: Nat, +c: Nat, +lands: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Land{f, F.Ok{c}}} : Maybe<&2, F.Leg>}, +ok: Bool) -> {pf.le(c, F.Sto.c(F.W.sto(F.St.w(F.step(s, F.Step{k, ok}))))) == True{} : Bool}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c2, +fr}:
              (cnt, all) = inv
              %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, cs, k), Some{F.Land{f, F.Ok{c}}}, lands) : {pf.le(c, F.Sto.c(F.W.sto(F.St.w(F.step.at(_, k, ok, F.W{F.Sto{c2, fr}, fl, ld, n}, cs))))) == True{} : Bool}
              LLogicLogic.pf.snd(pf.Lead(fl, ld, f), pf.Kept(F.Ok{c}, F.Sto{c2, fr}), pf.all_get(F.W{F.Sto{c2, fr}, fl, ld, n}, cs, k, F.Land{f, F.Ok{c}}, lands, all))

# a credential about to land is stored, or a newer one
def pf.Kept_orig(o: F.Out, +s: F.Sto) -> Type:
  match o:
    case F.Ok{c}:
      {F.le(c, F.Sto.c(s)) == True{} : Bool}
    case F.Err{e}:
      Unit

def pf.Good_orig(w: F.W, l: F.Leg) -> Type:
  match w:
    case F.W{+s, +fl, +ld, n}:
      match l:
        case F.Load{}:
          Unit
        case F.Board{}:
          Unit
        case F.Check{f}:
          pf.Lead(fl, ld, f)
        case F.Fetch{f}:
          pf.Lead(fl, ld, f)
        case F.Store{f, c}:
          pf.Lead(fl, ld, f)
        case F.Land{f, o}:
          (pf.Lead(fl, ld, f) & pf.Kept_orig(o, s))
        case F.Waiting{f}:
          Unit
        case F.Served{v, o}:
          pf.Got(ld, v, o)

def pf.All_orig(+w: F.W, cs: List<&2, F.Leg>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case l <> t:
      (pf.Good_orig(w, l) & pf.All_orig(w, t))

def auth_flight.pf.Inv_orig(s: F.St) -> Type:
  match s:
    case F.St{+w, +cs}:
      ({pf.leads(cs) == pf.holds(F.W.fl(w)) : Nat} & pf.All_orig(w, cs))

# the stored credential expires: it stays the stored one
def pf.kept_expire_orig(o: F.Out, +c: Nat, +fr: Bool, k: pf.Kept_orig(o, F.Sto{c, fr})) -> pf.Kept_orig(o, F.Sto{c, False{}}):
  match o:
    case F.Ok{c2}:
      k
    case F.Err{e}:
      Unit{}

def pf.good_expire_orig(+c: Nat, +fr: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, g: pf.Good_orig(F.W{F.Sto{c, fr}, fl, ld, n}, l)) -> pf.Good_orig(F.W{F.Sto{c, False{}}, fl, ld, n}, l):
  match l:
    case F.Load{}:
      Unit{}
    case F.Board{}:
      Unit{}
    case F.Check{f}:
      g
    case F.Fetch{f}:
      g
    case F.Store{f, c2}:
      g
    case F.Land{f, o}:
      (lead, k) = g
      (lead, pf.kept_expire_orig(o, c, fr, k))
    case F.Waiting{f}:
      Unit{}
    case F.Served{v, o}:
      g

def pf.all_expire_orig(+c: Nat, +fr: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, a: pf.All_orig(F.W{F.Sto{c, fr}, fl, ld, n}, cs)) -> pf.All_orig(F.W{F.Sto{c, False{}}, fl, ld, n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case h <> t:
      (gh, at) = a
      (pf.good_expire_orig(c, fr, fl, ld, n, h, gh), pf.all_expire_orig(c, fr, fl, ld, n, t, at))

def pf.all_join_orig(+w: F.W, pre: List<&2, F.Leg>, -l: F.Leg, -post: List<&2, F.Leg>, ap: pf.All_orig(w, pre), gl: pf.Good_orig(w, l), aq: pf.All_orig(w, post)) -> pf.All_orig(w, List.append(&2, F.Leg, pre, l <> post)):
  match pre:
    case Nil{}:
      (gl, aq)
    case h <> t:
      (gh, at) = ap
      (gh, pf.all_join_orig(w, t, l, post, at, gl, aq))

def auth_flight.pf.le_succ_orig(a: Nat, b: Nat, h: {F.le(a, b) == True{} : Bool}) -> {F.le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      auth_flight.pf.absurdF({F.le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      auth_flight.pf.le_succ_orig(p, q, h)

# a peer stores a newer credential
def pf.kept_peer_orig(o: F.Out, +c: Nat, +fr: Bool, k: pf.Kept_orig(o, F.Sto{c, fr})) -> pf.Kept_orig(o, F.Sto{1n+c, True{}}):
  match o:
    case F.Ok{c2}:
      auth_flight.pf.le_succ_orig(c2, c, k)
    case F.Err{e}:
      Unit{}

def pf.good_peer_orig(+c: Nat, +fr: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, g: pf.Good_orig(F.W{F.Sto{c, fr}, fl, ld, n}, l)) -> pf.Good_orig(F.W{F.Sto{1n+c, True{}}, fl, ld, n}, l):
  match l:
    case F.Load{}:
      Unit{}
    case F.Board{}:
      Unit{}
    case F.Check{f}:
      g
    case F.Fetch{f}:
      g
    case F.Store{f, c2}:
      g
    case F.Land{f, o}:
      (lead, k) = g
      (lead, pf.kept_peer_orig(o, c, fr, k))
    case F.Waiting{f}:
      Unit{}
    case F.Served{v, o}:
      g

def pf.all_peer_orig(+c: Nat, +fr: Bool, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, a: pf.All_orig(F.W{F.Sto{c, fr}, fl, ld, n}, cs)) -> pf.All_orig(F.W{F.Sto{1n+c, True{}}, fl, ld, n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case h <> t:
      (gh, at) = a
      (pf.good_peer_orig(c, fr, fl, ld, n, h, gh), pf.all_peer_orig(c, fr, fl, ld, n, t, at))

def pf.all_split.cons_orig(+w: F.W, -h: F.Leg, -t: List<&2, F.Leg>, -l: F.Leg, -post: List<&2, F.Leg>, gh: pf.Good_orig(w, h), r: (pf.All_orig(w, t) & (pf.Good_orig(w, l) & pf.All_orig(w, post)))) -> (pf.All_orig(w, h <> t) & (pf.Good_orig(w, l) & pf.All_orig(w, post))):
  (ap, rest) = r
  ((gh, ap), rest)

def pf.all_split_orig(+w: F.W, pre: List<&2, F.Leg>, -l: F.Leg, -post: List<&2, F.Leg>, a: pf.All_orig(w, List.append(&2, F.Leg, pre, l <> post))) -> (pf.All_orig(w, pre) & (pf.Good_orig(w, l) & pf.All_orig(w, post))):
  match pre:
    case Nil{}:
      (Unit{}, a)
    case h <> t:
      (gh, at) = a
      pf.all_split.cons_orig(w, h, t, l, post, gh, pf.all_split_orig(w, t, l, post, at))

def auth_flight.pf.le_refl_orig(n: Nat) -> {F.le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      auth_flight.pf.le_refl_orig(p)

# a fetch counts: no leg depends on the count
def pf.good_fetch_orig(+s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, g: pf.Good_orig(F.W{s, fl, ld, n}, l)) -> pf.Good_orig(F.W{s, fl, ld, 1n+n}, l):
  match l:
    case F.Load{}:
      g
    case F.Board{}:
      g
    case F.Check{f}:
      g
    case F.Fetch{f}:
      g
    case F.Store{f, c}:
      g
    case F.Land{f, o}:
      g
    case F.Waiting{f}:
      g
    case F.Served{v, o}:
      g

def pf.all_fetch_orig(+s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, a: pf.All_orig(F.W{s, fl, ld, n}, cs)) -> pf.All_orig(F.W{s, fl, ld, 1n+n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case h <> t:
      (gh, at) = a
      (pf.good_fetch_orig(s, fl, ld, n, h, gh), pf.all_fetch_orig(s, fl, ld, n, t, at))

def pf.good_land_orig(+s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +o: F.Out, +n: Nat, l: F.Leg, z: {pf.lead(l) == 0n : Nat}, g: pf.Good_orig(F.W{s, fl, ld, n}, l)) -> pf.Good_orig(F.W{s, False{}, List.append(&2, F.Out, ld, [o]), n}, l):
  match l:
    case F.Load{}:
      Unit{}
    case F.Board{}:
      Unit{}
    case F.Check{f}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(False{}, List.append(&2, F.Out, ld, [o]), f), 0n, z)
    case F.Fetch{f}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(False{}, List.append(&2, F.Out, ld, [o]), f), 0n, z)
    case F.Store{f, c}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(False{}, List.append(&2, F.Out, ld, [o]), f), 0n, z)
    case F.Land{f, o3}:
      LLogicLogic.pf.succ_ne_zero((pf.Lead(False{}, List.append(&2, F.Out, ld, [o]), f) & pf.Kept_orig(o3, s)), 0n, z)
    case F.Waiting{f}:
      Unit{}
    case F.Served{v, o2}:
      pf.got_land(ld, o, v, o2, g)

def pf.all_land_orig(+s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +o: F.Out, +n: Nat, cs: List<&2, F.Leg>, +z: {pf.leads(cs) == 0n : Nat}, a: pf.All_orig(F.W{s, fl, ld, n}, cs)) -> pf.All_orig(F.W{s, False{}, List.append(&2, F.Out, ld, [o]), n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case +h <> +t:
      (gh, at) = a
      (pf.good_land_orig(s, fl, ld, o, n, h, pf.fst({pf.lead(h) == 0n : Nat}, {pf.leads(t) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.lead(h), pf.leads(t), z)), gh), pf.all_land_orig(s, fl, ld, o, n, t, LLogicLogic.pf.snd({pf.lead(h) == 0n : Nat}, {pf.leads(t) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.lead(h), pf.leads(t), z)), at))

# the invariant of a world and callers that are one list split at a leg
def pf.inv_of_orig(+w: F.W, +pre: List<&2, F.Leg>, +l: F.Leg, +post: List<&2, F.Leg>, n: {Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))) == pf.holds(F.W.fl(w)) : Nat}, ap: pf.All_orig(w, pre), gl: pf.Good_orig(w, l), aq: pf.All_orig(w, post)) -> auth_flight.pf.Inv_orig(F.St{w, List.append(&2, F.Leg, pre, l <> post)}):
  (Equal.trans(Nat, pf.leads(List.append(&2, F.Leg, pre, l <> post)), Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))), pf.holds(F.W.fl(w)), pf.leads_append(pre, l <> post), n), pf.all_join_orig(w, pre, l, post, ap, gl, aq))

# the leader lands: no other caller leads, and no flight is in flight
def pf.core.land_orig(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, +f: Nat, +o: F.Out, +s: F.Sto, fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +i: {Nat.add(pf.leads(pre), 1n+pf.leads(post)) == pf.holds(fl) : Nat}, ap: pf.All_orig(F.W{s, fl, ld, n}, pre), gl: (pf.Lead(fl, ld, f) & pf.Kept_orig(o, s)), aq: pf.All_orig(F.W{s, fl, ld, n}, post)) -> auth_flight.pf.Inv_orig(F.St{F.W{s, False{}, List.append(&2, F.Out, ld, [o]), n}, List.append(&2, F.Leg, pre, F.Served{Some{f}, o} <> post)}):
  match fl:
    case True{}:
      (lead, kept) = gl
      (efl, ef) = lead
      +zp = pf.fst({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, pf.add_one(pf.leads(pre), pf.leads(post), i))
      +zq = LLogicLogic.pf.snd({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, pf.add_one(pf.leads(pre), pf.leads(post), i))
      pf.inv_of_orig(F.W{s, False{}, List.append(&2, F.Out, ld, [o]), n}, pre, F.Served{Some{f}, o}, post, pf.zero_sum(pf.leads(pre), pf.leads(post), zp, zq), pf.all_land_orig(s, True{}, ld, o, n, pre, zp, ap), pf.core.land.got(f, ld, o, ef), pf.all_land_orig(s, True{}, ld, o, n, post, zq, aq))
    case False{}:
      (lead, kept) = gl
      (e, _) = lead
      auth_flight.pf.absurdF(auth_flight.pf.Inv_orig(F.St{F.W{s, False{}, List.append(&2, F.Out, ld, [o]), n}, List.append(&2, F.Leg, pre, F.Served{Some{f}, o} <> post)}), e)

# a flight starts: no leader was in flight
def pf.good_flon_orig(+s: F.Sto, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, g: pf.Good_orig(F.W{s, False{}, ld, n}, l)) -> pf.Good_orig(F.W{s, True{}, ld, n}, l):
  match l:
    case F.Load{}:
      Unit{}
    case F.Board{}:
      Unit{}
    case F.Check{f}:
      (e, _) = g
      auth_flight.pf.absurdF(pf.Lead(True{}, ld, f), e)
    case F.Fetch{f}:
      (e, _) = g
      auth_flight.pf.absurdF(pf.Lead(True{}, ld, f), e)
    case F.Store{f, c}:
      (e, _) = g
      auth_flight.pf.absurdF(pf.Lead(True{}, ld, f), e)
    case F.Land{f, o}:
      (lead, _) = g
      (e, _) = lead
      auth_flight.pf.absurdF((pf.Lead(True{}, ld, f) & pf.Kept_orig(o, s)), e)
    case F.Waiting{f}:
      Unit{}
    case F.Served{v, o}:
      g

def pf.all_flon_orig(+s: F.Sto, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, a: pf.All_orig(F.W{s, False{}, ld, n}, cs)) -> pf.All_orig(F.W{s, True{}, ld, n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case h <> t:
      (gh, at) = a
      (pf.good_flon_orig(s, ld, n, h, gh), pf.all_flon_orig(s, ld, n, t, at))

# a caller boards and no flight is in flight: it starts the next flight
def pf.core.start_orig(+s: F.Sto, +ld: List<&2, F.Out>, +n: Nat, +pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, +i: {Nat.add(pf.leads(pre), pf.leads(post)) == 0n : Nat}, ap: pf.All_orig(F.W{s, False{}, ld, n}, pre), aq: pf.All_orig(F.W{s, False{}, ld, n}, post)) -> auth_flight.pf.Inv_orig(F.St{F.W{s, True{}, ld, n}, List.append(&2, F.Leg, pre, F.Check{List.length(&2, F.Out, ld)} <> post)}):
  +zp = pf.fst({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.leads(pre), pf.leads(post), i))
  +zq = LLogicLogic.pf.snd({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.leads(pre), pf.leads(post), i))
  pf.inv_of_orig(F.W{s, True{}, ld, n}, pre, F.Check{List.length(&2, F.Out, ld)}, post, pf.core.start.count(pf.leads(pre), pf.leads(post), zp, zq), pf.all_flon_orig(s, ld, n, pre, ap), ({==}, {==}), pf.all_flon_orig(s, ld, n, post, aq))

# the leader stores: no other caller leads
def pf.good_store_orig(+s1: F.Sto, +s2: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, l: F.Leg, z: {pf.lead(l) == 0n : Nat}, g: pf.Good_orig(F.W{s1, fl, ld, n}, l)) -> pf.Good_orig(F.W{s2, fl, ld, n}, l):
  match l:
    case F.Load{}:
      Unit{}
    case F.Board{}:
      Unit{}
    case F.Check{f}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(fl, ld, f), 0n, z)
    case F.Fetch{f}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(fl, ld, f), 0n, z)
    case F.Store{f, c}:
      LLogicLogic.pf.succ_ne_zero(pf.Lead(fl, ld, f), 0n, z)
    case F.Land{f, o}:
      LLogicLogic.pf.succ_ne_zero((pf.Lead(fl, ld, f) & pf.Kept_orig(o, s2)), 0n, z)
    case F.Waiting{f}:
      Unit{}
    case F.Served{v, o}:
      g

def pf.all_store_orig(+s1: F.Sto, +s2: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, cs: List<&2, F.Leg>, +z: {pf.leads(cs) == 0n : Nat}, a: pf.All_orig(F.W{s1, fl, ld, n}, cs)) -> pf.All_orig(F.W{s2, fl, ld, n}, cs):
  match cs:
    case Nil{}:
      Unit{}
    case +h <> +t:
      (gh, at) = a
      (pf.good_store_orig(s1, s2, fl, ld, n, h, pf.fst({pf.lead(h) == 0n : Nat}, {pf.leads(t) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.lead(h), pf.leads(t), z)), gh), pf.all_store_orig(s1, s2, fl, ld, n, t, LLogicLogic.pf.snd({pf.lead(h) == 0n : Nat}, {pf.leads(t) == 0n : Nat}, LLogicNat.auth_flight.pf.add_zero(pf.lead(h), pf.leads(t), z)), at))

# the leader stores the fetched credential: no other caller leads
def pf.core.store_orig(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, +f: Nat, +c: Nat, +x: Nat, fl: Bool, +ld: List<&2, F.Out>, +n: Nat, +i: {Nat.add(pf.leads(pre), 1n+pf.leads(post)) == pf.holds(fl) : Nat}, ap: pf.All_orig(F.W{F.Sto{x, False{}}, fl, ld, n}, pre), gl: pf.Lead(fl, ld, f), aq: pf.All_orig(F.W{F.Sto{x, False{}}, fl, ld, n}, post)) -> auth_flight.pf.Inv_orig(F.St{F.W{F.Sto{c, True{}}, fl, ld, n}, List.append(&2, F.Leg, pre, F.Land{f, F.Ok{c}} <> post)}):
  match fl:
    case True{}:
      +zp = pf.fst({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, pf.add_one(pf.leads(pre), pf.leads(post), i))
      +zq = LLogicLogic.pf.snd({pf.leads(pre) == 0n : Nat}, {pf.leads(post) == 0n : Nat}, pf.add_one(pf.leads(pre), pf.leads(post), i))
      pf.inv_of_orig(F.W{F.Sto{c, True{}}, True{}, ld, n}, pre, F.Land{f, F.Ok{c}}, post, i, pf.all_store_orig(F.Sto{x, False{}}, F.Sto{c, True{}}, True{}, ld, n, pre, zp, ap), (gl, auth_flight.pf.le_refl_orig(c)), pf.all_store_orig(F.Sto{x, False{}}, F.Sto{c, True{}}, True{}, ld, n, post, zq, aq))
    case False{}:
      (e, _) = gl
      auth_flight.pf.absurdF(auth_flight.pf.Inv_orig(F.St{F.W{F.Sto{c, True{}}, False{}, ld, n}, List.append(&2, F.Leg, pre, F.Land{f, F.Ok{c}} <> post)}), e)

# a caller that joined a flight takes its outcome once it landed
def pf.core.wait_orig(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, +f: Nat, +s: F.Sto, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat, m: Maybe<&2, F.Out>, e: {List.get(&2, F.Out, ld, f) == m : Maybe<&2, F.Out>}, i: {Nat.add(pf.leads(pre), pf.leads(post)) == pf.holds(fl) : Nat}, ap: pf.All_orig(F.W{s, fl, ld, n}, pre), aq: pf.All_orig(F.W{s, fl, ld, n}, post)) -> auth_flight.pf.Inv_orig(F.St{F.Adv.w(F.adv.wait.got(f, m, F.W{s, fl, ld, n})), List.append(&2, F.Leg, pre, F.Adv.l(F.adv.wait.got(f, m, F.W{s, fl, ld, n})) <> post)}):
  match m:
    case None{}:
      pf.inv_of_orig(F.W{s, fl, ld, n}, pre, F.Waiting{f}, post, i, ap, Unit{}, aq)
    case Some{+o}:
      pf.inv_of_orig(F.W{s, fl, ld, n}, pre, F.Served{Some{f}, o}, post, i, ap, e, aq)

# one caller's step, between the callers before it and after it
def pf.core_orig(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, l: F.Leg, w: F.W, ok: Bool, i: {Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))) == pf.holds(F.W.fl(w)) : Nat}, ap: pf.All_orig(w, pre), gl: pf.Good_orig(w, l), aq: pf.All_orig(w, post)) -> auth_flight.pf.Inv_orig(F.St{F.Adv.w(F.adv(l, ok, w)), List.append(&2, F.Leg, pre, F.Adv.l(F.adv(l, ok, w)) <> post)}):
  match l:
    case F.Load{}:
      match w:
        case F.W{s, +fl, +ld, +n}:
          match s:
            case F.Sto{+c, fr}:
              match fr:
                case True{}:
                  pf.inv_of_orig(F.W{F.Sto{c, True{}}, fl, ld, n}, pre, F.Served{None{}, F.Ok{c}}, post, i, ap, Unit{}, aq)
                case False{}:
                  pf.inv_of_orig(F.W{F.Sto{c, False{}}, fl, ld, n}, pre, F.Board{}, post, i, ap, Unit{}, aq)
    case F.Board{}:
      match w:
        case F.W{+s, fl, +ld, +n}:
          match fl:
            case True{}:
              pf.inv_of_orig(F.W{s, True{}, ld, n}, pre, F.Waiting{List.length(&2, F.Out, ld)}, post, i, ap, Unit{}, aq)
            case False{}:
              pf.core.start_orig(s, ld, n, pre, post, i, ap, aq)
    case F.Check{+f}:
      match w:
        case F.W{s, +fl, +ld, +n}:
          match s:
            case F.Sto{+c, fr}:
              match fr:
                case True{}:
                  pf.inv_of_orig(F.W{F.Sto{c, True{}}, fl, ld, n}, pre, F.Land{f, F.Ok{c}}, post, i, ap, (gl, auth_flight.pf.le_refl_orig(c)), aq)
                case False{}:
                  pf.inv_of_orig(F.W{F.Sto{c, False{}}, fl, ld, n}, pre, F.Fetch{f}, post, i, ap, gl, aq)
    case F.Fetch{+f}:
      match w:
        case F.W{+s, +fl, +ld, +n}:
          match ok:
            case True{}:
              pf.inv_of_orig(F.W{s, fl, ld, 1n+n}, pre, F.Store{f, 1n+n}, post, i, pf.all_fetch_orig(s, fl, ld, n, pre, ap), gl, pf.all_fetch_orig(s, fl, ld, n, post, aq))
            case False{}:
              pf.inv_of_orig(F.W{s, fl, ld, 1n+n}, pre, F.Land{f, F.Err{1n+n}}, post, i, pf.all_fetch_orig(s, fl, ld, n, pre, ap), (gl, Unit{}), pf.all_fetch_orig(s, fl, ld, n, post, aq))
    case F.Store{+f, +c}:
      match w:
        case F.W{s, fl, +ld, +n}:
          match s:
            case F.Sto{+p, fr}:
              match fr:
                case True{}:
                  pf.inv_of_orig(F.W{F.Sto{p, True{}}, fl, ld, n}, pre, F.Land{f, F.Ok{p}}, post, i, ap, (gl, auth_flight.pf.le_refl_orig(p)), aq)
                case False{}:
                  pf.core.store_orig(pre, post, f, c, p, fl, ld, n, i, ap, gl, aq)
    case F.Land{+f, +o}:
      match w:
        case F.W{+s, fl, +ld, +n}:
          pf.core.land_orig(pre, post, f, o, s, fl, ld, n, i, ap, gl, aq)
    case F.Waiting{+f}:
      match w:
        case F.W{+s, +fl, +ld, +n}:
          pf.core.wait_orig(pre, post, f, s, fl, ld, n, List.get(&2, F.Out, ld, f), {==}, i, ap, aq)
    case F.Served{+v, +o}:
      pf.inv_of_orig(w, pre, F.Served{v, o}, post, i, ap, gl, aq)

def pf.inv_core.parts_orig(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, l: F.Leg, w: F.W, ok: Bool, i: {Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))) == pf.holds(F.W.fl(w)) : Nat}, parts: (pf.All_orig(w, pre) & (pf.Good_orig(w, l) & pf.All_orig(w, post)))) -> auth_flight.pf.Inv_orig(F.St{F.Adv.w(F.adv(l, ok, w)), List.append(&2, F.Leg, pre, F.Adv.l(F.adv(l, ok, w)) <> post)}):
  (ap, rest) = parts
  (gl, aq) = rest
  pf.core_orig(pre, post, l, w, ok, i, ap, gl, aq)

def pf.inv_core_orig(+pre: List<&2, F.Leg>, +post: List<&2, F.Leg>, +l: F.Leg, +w: F.W, ok: Bool, inv: auth_flight.pf.Inv_orig(F.St{w, List.append(&2, F.Leg, pre, l <> post)})) -> auth_flight.pf.Inv_orig(F.St{F.Adv.w(F.adv(l, ok, w)), List.append(&2, F.Leg, pre, F.Adv.l(F.adv(l, ok, w)) <> post)}):
  (cnt, all) = inv
  pf.inv_core.parts_orig(pre, post, l, w, ok, Equal.trans(Nat, Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))), pf.leads(List.append(&2, F.Leg, pre, l <> post)), pf.holds(F.W.fl(w)), Equal.sym(Nat, pf.leads(List.append(&2, F.Leg, pre, l <> post)), Nat.add(pf.leads(pre), Nat.add(pf.lead(l), pf.leads(post))), pf.leads_append(pre, l <> post)), cnt), pf.all_split_orig(w, pre, l, post, all))

def pf.inv_cs_orig(+w: F.W, -cs: List<&2, F.Leg>, -xs: List<&2, F.Leg>, e: {cs == xs : List<&2, F.Leg>}, inv: auth_flight.pf.Inv_orig(F.St{w, cs})) -> auth_flight.pf.Inv_orig(F.St{w, xs}):
  %e : auth_flight.pf.Inv_orig(F.St{w, _})
  inv

def pf.inv_at_orig(m: Maybe<&2, F.Leg>, +k: Nat, +ok: Bool, +w: F.W, +cs: List<&2, F.Leg>, g: {List.get(&2, F.Leg, cs, k) == m : Maybe<&2, F.Leg>}, inv: auth_flight.pf.Inv_orig(F.St{w, cs})) -> auth_flight.pf.Inv_orig(F.step.at(m, k, ok, w, cs)):
  match m:
    case None{}:
      inv
    case Some{+l}:
      %pf.put_eta(k, F.adv(l, ok, w), cs) : auth_flight.pf.Inv_orig(_)
      pf.inv_core_orig(List.take(&2, F.Leg, cs, k), List.drop(&2, F.Leg, cs, 1n+k), l, w, ok, pf.inv_cs_orig(w, cs, List.append(&2, F.Leg, List.take(&2, F.Leg, cs, k), l <> List.drop(&2, F.Leg, cs, 1n+k)), pf.split(F.Leg, F.Load{}, cs, k, l, g), inv))

def pf.inv_step_orig(s: F.St, e: F.Ev, inv: auth_flight.pf.Inv_orig(s)) -> auth_flight.pf.Inv_orig(F.step(s, e)):
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c, +fr}:
              match e:
                case F.Arrive{}:
                  (cnt, all) = inv
                  (Equal.trans(Nat, pf.leads(List.append(&2, F.Leg, cs, [F.Load{}])), pf.leads(cs), pf.holds(fl), Equal.trans(Nat, pf.leads(List.append(&2, F.Leg, cs, [F.Load{}])), Nat.add(pf.leads(cs), 0n), pf.leads(cs), pf.leads_append(cs, [F.Load{}]), pf.add_zero_r(pf.leads(cs))), cnt), pf.all_join_orig(F.W{F.Sto{c, fr}, fl, ld, n}, cs, F.Load{}, Nil{}, all, Unit{}, Unit{}))
                case F.Step{+k, ok}:
                  pf.inv_at_orig(List.get(&2, F.Leg, cs, k), k, ok, F.W{F.Sto{c, fr}, fl, ld, n}, cs, {==}, inv)
                case F.Peer{}:
                  (cnt, all) = inv
                  (cnt, pf.all_peer_orig(c, fr, fl, ld, n, cs, all))
                case F.Expire{}:
                  (cnt, all) = inv
                  (cnt, pf.all_expire_orig(c, fr, fl, ld, n, cs, all))

def pf.inv_go_orig(evs: List<&2, F.Ev>, +s: F.St, inv: auth_flight.pf.Inv_orig(s)) -> auth_flight.pf.Inv_orig(F.go(evs, s)):
  match evs:
    case Nil{}:
      inv
    case +e <> rest:
      pf.inv_go_orig(rest, F.step(s, e), pf.inv_step_orig(s, e, inv))

def pf.inv_run_orig(evs: List<&2, F.Ev>) -> auth_flight.pf.Inv_orig(F.run(evs)):
  pf.inv_go_orig(evs, F.St.new(), ({==}, Unit{}))

def pf.all_get_orig(+w: F.W, cs: List<&2, F.Leg>, k: Nat, -x: F.Leg, g: {List.get(&2, F.Leg, cs, k) == Some{x} : Maybe<&2, F.Leg>}, a: pf.All_orig(w, cs)) -> pf.Good_orig(w, x):
  match cs k:
    case Nil{} _:
      pf.none_some(F.Leg, pf.Good_orig(w, x), x, g)
    case +h <> t 0n:
      (gh, at) = a
      %pf.some_inj(F.Leg, F.Load{}, h, x, g) : pf.Good_orig(w, _)
      gh
    case h <> t 1n+p:
      (gh, at) = a
      pf.all_get_orig(w, t, p, x, g, at)

def pf.stored_orig(s: F.St, inv: auth_flight.pf.Inv_orig(s), +k: Nat, +f: Nat, +c: Nat, +lands: {List.get(&2, F.Leg, F.St.cs(s), k) == Some{F.Land{f, F.Ok{c}}} : Maybe<&2, F.Leg>}, +ok: Bool) -> {F.le(c, F.Sto.c(F.W.sto(F.St.w(F.step(s, F.Step{k, ok}))))) == True{} : Bool}:
  match s:
    case F.St{w, +cs}:
      match w:
        case F.W{sto, +fl, +ld, +n}:
          match sto:
            case F.Sto{+c2, +fr}:
              (cnt, all) = inv
              %Equal.sym(Maybe<&2, F.Leg>, List.get(&2, F.Leg, cs, k), Some{F.Land{f, F.Ok{c}}}, lands) : {F.le(c, F.Sto.c(F.W.sto(F.St.w(F.step.at(_, k, ok, F.W{F.Sto{c2, fr}, fl, ld, n}, cs))))) == True{} : Bool}
              LLogicLogic.pf.snd(pf.Lead(fl, ld, f), pf.Kept_orig(F.Ok{c}, F.Sto{c2, fr}), pf.all_get_orig(F.W{F.Sto{c2, fr}, fl, ld, n}, cs, k, F.Land{f, F.Ok{c}}, lands, all))
