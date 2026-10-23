# eukhe: the proof of LAW list_one_location

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

# Listing
# -------

def pg.or_mono(a: Bool, -x: Bool, -y: Bool, h: {Bool.or(a, x) == True{} : Bool}, f: {x == True{} : Bool} -> {y == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

def pg.or_r(a: Bool, -y: Bool, h: {y == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# a storage listed is a directory of that name
def pg.dur_put(+m: Nat, +n: Nat, -d: List<&2, Nat>, -r: List<&2, Sg.Ent>, q: Bool, h: {Sg.mem(n, Sg.keep.put(m, d, q)) == True{} : Bool}, ih: {Sg.mem(n, d) == True{} : Bool} -> {Sg.dirn(n, r) == True{} : Bool}) -> {Bool.or(Nat.is_eq(m, n), Sg.dirn(n, r)) == True{} : Bool}:
  match q:
    case True{}:
      pg.or_mono(Nat.is_eq(m, n), Sg.mem(n, d), Sg.dirn(n, r), h, ih)
    case False{}:
      pg.or_r(Nat.is_eq(m, n), Sg.dirn(n, r), ih(h))

def pg.dur_dirn(+n: Nat, es: List<&2, Sg.Ent>, h: {Sg.mem(n, Sg.durables(es)) == True{} : Bool}) -> {Sg.dirn(n, es) == True{} : Bool}:
  match es:
    case Nil{}:
      LA.pg.absurd({Sg.dirn(n, Nil{}) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case e <> +rest:
      match e:
        case Sg.Dir{+m, a, hd, c}:
          pg.dur_put(m, n, Sg.durables(rest), rest, Bool.and(a, Bool.and(Bool.not(hd), c)), h, hh => pg.dur_dirn(n, rest, hh))
        case Sg.Legacy{s, r}:
          pg.dur_dirn(n, rest, h)

def pg.and_not(r: Bool, d: Bool, h: {Bool.and(r, Bool.not(d)) == True{} : Bool}) -> {d == False{} : Bool}:
  match r d:
    case True{} True{}:
      LA.pg.absurd({True{} == False{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case True{} False{}:
      {==}
    case False{} True{}:
      LA.pg.absurd({True{} == False{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case False{} False{}:
      {==}

def pg.leg_hit(-all: List<&2, Sg.Ent>, +n: Nat, +s: Nat, -l: List<&2, Nat>, b: Bool, eb: {Nat.is_eq(s, n) == b : Bool}, h: {Bool.or(b, Sg.mem(n, l)) == True{} : Bool}, nd: {Sg.dirn(s, all) == False{} : Bool}, ih: {Sg.mem(n, l) == True{} : Bool} -> {Sg.dirn(n, all) == False{} : Bool}) -> {Sg.dirn(n, all) == False{} : Bool}:
  match b:
    case True{}:
      %LA.pg.eq_true(s, n, eb) : {Sg.dirn(_, all) == False{} : Bool}
      nd
    case False{}:
      ih(h)

def pg.leg_put(+all: List<&2, Sg.Ent>, +n: Nat, +s: Nat, +r: Bool, -l: List<&2, Nat>, q: Bool, eq: {Bool.and(r, Bool.not(Sg.dirn(s, all))) == q : Bool}, h: {Sg.mem(n, Sg.keep.put(s, l, q)) == True{} : Bool}, ih: {Sg.mem(n, l) == True{} : Bool} -> {Sg.dirn(n, all) == False{} : Bool}) -> {Sg.dirn(n, all) == False{} : Bool}:
  match q:
    case True{}:
      pg.leg_hit(all, n, s, l, Nat.is_eq(s, n), {==}, h, pg.and_not(r, Sg.dirn(s, all), eq), ih)
    case False{}:
      ih(h)

# a legacy file listed has no directory of its name
def pg.leg_dirn(+all: List<&2, Sg.Ent>, +n: Nat, es: List<&2, Sg.Ent>, h: {Sg.mem(n, Sg.legacies(all, es)) == True{} : Bool}) -> {Sg.dirn(n, all) == False{} : Bool}:
  match es:
    case Nil{}:
      LA.pg.absurd({Sg.dirn(n, all) == False{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case e <> +rest:
      match e:
        case Sg.Dir{m, a, hd, c}:
          pg.leg_dirn(all, n, rest, h)
        case Sg.Legacy{+s, +r}:
          pg.leg_put(all, n, s, r, Sg.legacies(all, rest), Bool.and(r, Bool.not(Sg.dirn(s, all))), {==}, h, hh => pg.leg_dirn(all, n, rest, hh))

def pg.one_go(+es: List<&2, Sg.Ent>, +n: Nat, b1: Bool, e1: {Sg.mem(n, Sg.durables(es)) == b1 : Bool}, b2: Bool, e2: {Sg.mem(n, Sg.legacies(es, es)) == b2 : Bool}) -> {Bool.and(b1, b2) == False{} : Bool}:
  match b1 b2:
    case True{} True{}:
      LA.pg.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, Sg.dirn(n, es), False{}, Equal.sym(Bool, Sg.dirn(n, es), True{}, pg.dur_dirn(n, es, e1)), pg.leg_dirn(es, n, es, e2)))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the law list_one_location
def pg.one_location(+es: List<&2, Sg.Ent>, +n: Nat) -> {Bool.and(Sg.mem(n, Sg.durables(es)), Sg.mem(n, Sg.legacies(es, es))) == False{} : Bool}:
  pg.one_go(es, n, Sg.mem(n, Sg.durables(es)), {==}, Sg.mem(n, Sg.legacies(es, es)), {==})

def Staging.list_one_location(es, n):
  pg.one_location(es, n)
