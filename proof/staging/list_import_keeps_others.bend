# eukhe: the proof of LAW list_import_keeps_others

import Base
import ../../bend/staging.bend as Sg
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pg.or_f(a: Bool) -> {a == Bool.or(a, False{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pg.dirn_app(+n: Nat, es: List<&2, Sg.Ent>, +x: List<&2, Sg.Ent>) -> {Bool.or(Sg.dirn(n, es), Sg.dirn(n, x)) == Sg.dirn(n, List.append(&2, Sg.Ent, es, x)) : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Sg.Dir{+m, a, hd, c}:
          %pg.dirn_app(n, rest, x) : {Bool.or(Bool.or(Nat.is_eq(m, n), Sg.dirn(n, rest)), Sg.dirn(n, x)) == Bool.or(Nat.is_eq(m, n), _) : Bool}
          LA.pg.or_assoc(Nat.is_eq(m, n), Sg.dirn(n, rest), Sg.dirn(n, x))
        case Sg.Legacy{st, r}:
          pg.dirn_app(n, rest, x)

# with the directory s added, dirn is the same for a name that is not s
def pg.dirn_other(+n: Nat, +all: List<&2, Sg.Ent>, +s: Nat, ne: {Nat.is_eq(s, n) == False{} : Bool}) -> {Sg.dirn(n, all) == Sg.dirn(n, Sg.imported(s, all)) : Bool}:
  %pg.dirn_app(n, all, [Sg.Dir{s, True{}, False{}, True{}}]) : {Sg.dirn(n, all) == _ : Bool}
  %Equal.sym(Bool, Nat.is_eq(s, n), False{}, ne) : {Sg.dirn(n, all) == Bool.or(Sg.dirn(n, all), Bool.or(_, False{})) : Bool}
  pg.or_f(Sg.dirn(n, all))

def pg.mem_miss(+st: Nat, +n: Nat, +l: List<&2, Nat>, q: Bool, ec: {Nat.is_eq(st, n) == False{} : Bool}) -> {Sg.mem(n, l) == Sg.mem(n, Sg.keep.put(st, l, q)) : Bool}:
  match q:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(st, n), False{}, ec) : {Sg.mem(n, l) == Bool.or(_, Sg.mem(n, l)) : Bool}
      {==}
    case False{}:
      {==}

def pg.mem_same(+n: Nat, +l1: List<&2, Nat>, +l2: List<&2, Nat>, q: Bool, ih: {Sg.mem(n, l1) == Sg.mem(n, l2) : Bool}) -> {Sg.mem(n, Sg.keep.put(n, l1, q)) == Sg.mem(n, Sg.keep.put(n, l2, q)) : Bool}:
  match q:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, LA.pg.eq_refl(n)) : {Bool.or(_, Sg.mem(n, l1)) == Bool.or(_, Sg.mem(n, l2)) : Bool}
      {==}
    case False{}:
      ih

def pg.leg_step(c: Bool, +st: Nat, +r: Bool, +n: Nat, +all: List<&2, Sg.Ent>, +s: Nat, +l1: List<&2, Nat>, +l2: List<&2, Nat>, +ec: {Nat.is_eq(st, n) == c : Bool}, ne: {Nat.is_eq(s, n) == False{} : Bool}, ih: {Sg.mem(n, l1) == Sg.mem(n, l2) : Bool}) -> {Sg.mem(n, Sg.keep.put(st, l1, Bool.and(r, Bool.not(Sg.dirn(st, Sg.imported(s, all)))))) == Sg.mem(n, Sg.keep.put(st, l2, Bool.and(r, Bool.not(Sg.dirn(st, all))))) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, st, n, LA.pg.eq_true(st, n, ec)) : {Sg.mem(n, Sg.keep.put(_, l1, Bool.and(r, Bool.not(Sg.dirn(_, Sg.imported(s, all)))))) == Sg.mem(n, Sg.keep.put(_, l2, Bool.and(r, Bool.not(Sg.dirn(_, all))))) : Bool}
      %pg.dirn_other(n, all, s, ne) : {Sg.mem(n, Sg.keep.put(n, l1, Bool.and(r, Bool.not(_)))) == Sg.mem(n, Sg.keep.put(n, l2, Bool.and(r, Bool.not(Sg.dirn(n, all))))) : Bool}
      pg.mem_same(n, l1, l2, Bool.and(r, Bool.not(Sg.dirn(n, all))), ih)
    case False{}:
      %pg.mem_miss(st, n, l1, Bool.and(r, Bool.not(Sg.dirn(st, Sg.imported(s, all)))), ec) : {_ == Sg.mem(n, Sg.keep.put(st, l2, Bool.and(r, Bool.not(Sg.dirn(st, all))))) : Bool}
      %pg.mem_miss(st, n, l2, Bool.and(r, Bool.not(Sg.dirn(st, all))), ec) : {Sg.mem(n, l1) == _ : Bool}
      ih

# the legacy files listed with the directory s added, for a name not s
def pg.leg_other(+all: List<&2, Sg.Ent>, +s: Nat, +n: Nat, ys: List<&2, Sg.Ent>, +ne: {Nat.is_eq(s, n) == False{} : Bool}) -> {Sg.mem(n, Sg.legacies(Sg.imported(s, all), ys)) == Sg.mem(n, Sg.legacies(all, ys)) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case y <> +rest:
      match y:
        case Sg.Dir{m, a, hd, c}:
          pg.leg_other(all, s, n, rest, ne)
        case Sg.Legacy{+st, +r}:
          pg.leg_step(Nat.is_eq(st, n), st, r, n, all, s, Sg.legacies(Sg.imported(s, all), rest), Sg.legacies(all, rest), {==}, ne, pg.leg_other(all, s, n, rest, ne))

def pg.leg_tail(+all: List<&2, Sg.Ent>, es: List<&2, Sg.Ent>, +x: List<&2, Sg.Ent>) -> {List.append(&2, Nat, Sg.legacies(all, es), Sg.legacies(all, x)) == Sg.legacies(all, List.append(&2, Sg.Ent, es, x)) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Sg.Dir{m, a, hd, c}:
          pg.leg_tail(all, rest, x)
        case Sg.Legacy{+st, +r}:
          +q = Bool.and(r, Bool.not(Sg.dirn(st, all)))
          %LA.pg.kput_app(st, Sg.legacies(all, rest), Sg.legacies(all, x), q) : {_ == Sg.keep.put(st, Sg.legacies(all, List.append(&2, Sg.Ent, rest, x)), q) : List<&2, Nat>}
          %pg.leg_tail(all, rest, x) : {Sg.keep.put(st, List.append(&2, Nat, Sg.legacies(all, rest), Sg.legacies(all, x)), q) == Sg.keep.put(st, _, q) : List<&2, Nat>}
          {==}

# the law list_import_keeps_others
def pg.app_nil(xs: List<&2, Nat>) -> {xs == List.append(&2, Nat, xs, Nil{}) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %pg.app_nil(rest) : {x <> rest == x <> _ : List<&2, Nat>}
      {==}

def pg.import_keeps(+es: List<&2, Sg.Ent>, +s: Nat, +n: Nat, +ne: {Nat.is_eq(s, n) == False{} : Bool}) -> {Sg.mem(n, Sg.listing(Sg.imported(s, es))) == Sg.mem(n, Sg.listing(es)) : Bool}:
  +d = {[Sg.Dir{s, True{}, False{}, True{}}] : List<&2, Sg.Ent>}
  +all = Sg.imported(s, es)
  +ds = List.append(&2, Nat, Sg.durables(es), [s])
  %LA.pg.dur_app(es, d) : {Sg.mem(n, List.append(&2, Nat, _, Sg.legacies(all, all))) == Sg.mem(n, Sg.listing(es)) : Bool}
  %pg.leg_tail(all, es, d) : {Sg.mem(n, List.append(&2, Nat, ds, _)) == Sg.mem(n, Sg.listing(es)) : Bool}
  %LA.pg.mem_app(n, ds, List.append(&2, Nat, Sg.legacies(all, es), Nil{})) : {_ == Sg.mem(n, Sg.listing(es)) : Bool}
  %pg.app_nil(Sg.legacies(all, es)) : {Bool.or(Sg.mem(n, ds), Sg.mem(n, _)) == Sg.mem(n, Sg.listing(es)) : Bool}
  %LA.pg.mem_app(n, Sg.durables(es), [s]) : {Bool.or(_, Sg.mem(n, Sg.legacies(all, es))) == Sg.mem(n, Sg.listing(es)) : Bool}
  %Equal.sym(Bool, Nat.is_eq(s, n), False{}, ne) : {Bool.or(Bool.or(Sg.mem(n, Sg.durables(es)), Bool.or(_, False{})), Sg.mem(n, Sg.legacies(all, es))) == Sg.mem(n, Sg.listing(es)) : Bool}
  %pg.or_f(Sg.mem(n, Sg.durables(es))) : {Bool.or(_, Sg.mem(n, Sg.legacies(all, es))) == Sg.mem(n, Sg.listing(es)) : Bool}
  %Equal.sym(Bool, Sg.mem(n, Sg.legacies(all, es)), Sg.mem(n, Sg.legacies(es, es)), pg.leg_other(es, s, n, es, ne)) : {Bool.or(Sg.mem(n, Sg.durables(es)), _) == Sg.mem(n, Sg.listing(es)) : Bool}
  LA.pg.mem_app(n, Sg.durables(es), Sg.legacies(es, es))

def Laws.list_import_keeps_others(es, s, n, ne):
  pg.import_keeps(es, s, n, ne)
