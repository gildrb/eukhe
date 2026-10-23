# eukhe: the proof of LAW config_needs_yes

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy.bend as PathPolicy
import ../base.bend as L
import ./base.bend as LA

def pp.or_false_l(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      L.pp.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pp.or_false_r(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      L.pp.absurd({b == False{} : Bool}, h)
    case False{}:
      h

def pp.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.pp.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LA.pp.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pp.eq_true(p, q, h))

def pp.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LA.pp.absurdF({False{} == True{} : Bool}, h)

# two lists that ids.eq calls equal are equal
def pp.ids_sound(a: List<&2, Nat>, b: List<&2, Nat>, +h: {Tl.ids.eq(a, b) == True{} : Bool}) -> {a == b : List<&2, Nat>}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case y <> yr:
          LA.pp.absurdF({Nil{} == y <> yr : List<&2, Nat>}, h)
    case +x <> +xr:
      match b:
        case Nil{}:
          LA.pp.absurdF({x <> xr == Nil{} : List<&2, Nat>}, h)
        case +y <> +yr:
          %pp.eq_true(x, y, pp.and_l(Nat.is_eq(x, y), Tl.ids.eq(xr, yr), h)) : {x <> xr == _ <> yr : List<&2, Nat>}
          %pp.ids_sound(xr, yr, LA.pp.and_r(Nat.is_eq(x, y), Tl.ids.eq(xr, yr), h)) : {x <> xr == x <> _ : List<&2, Nat>}
          {==}

# 4. The store
# ------------

def pp.inside_unguarded(c: Pp.Cls, h: {Pp.Cls.inside(c) == True{} : Bool}) -> {Pp.Cls.guarded(c) == False{} : Bool}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      LA.pp.absurdF({False{} == False{} : Bool}, h)
    case Pp.Protected{}:
      LA.pp.absurdF({True{} == False{} : Bool}, h)
    case Pp.Secret{}:
      LA.pp.absurdF({True{} == False{} : Bool}, h)

# the real location of a path judged Inside is not guarded
def pp.inside_res(+pol: Pp.Pol, r: Pp.Res, h: {Pp.class_res(pol, r) == Pp.Inside{} : Pp.Cls}) -> {Pp.Cls.guarded(Pp.class_of(pol, Pp.Res.at(r))) == False{} : Bool}:
  match r:
    case Pp.Res{+at, +looped}:
      pp.inside_unguarded(Pp.class_of(pol, at), LA.pp.and_r(Bool.not(looped), Pp.Cls.inside(Pp.class_of(pol, at)), LA.pp.demote_inside(Pp.class_of(pol, at), looped, h)))

# one cell of a set, by the head test b
def pp.set_pick(b: Bool, +c: Pp.Cell, +rest: List<&2, Pp.Cell>, +pol: Pp.Pol, +k: List<&2, Nat>, +v: Nat, e: {Tl.ids.eq(Pp.Cell.at(c), k) == b : Bool}, +hk: {Pp.Cls.guarded(Pp.class_of(pol, k)) == False{} : Bool}, ih: {Pp.guarded(Pp.set(rest, k, v), pol) == Pp.guarded(rest, pol) : List<&2, Pp.Cell>}) -> {Pp.guarded(Pp.set.pick(b, c, k, v, rest, Pp.set(rest, k, v)), pol) == Pp.guarded(c <> rest, pol) : List<&2, Pp.Cell>}:
  match b:
    case True{}:
      +same = pp.ids_sound(Pp.Cell.at(c), k, e)
      %Equal.sym(Bool, Pp.Cls.guarded(Pp.class_of(pol, k)), False{}, hk) : {Pp.keep.pick(_, Pp.Cell{k, v}, Pp.guarded(rest, pol)) == Pp.guarded(c <> rest, pol) : List<&2, Pp.Cell>}
      %Equal.sym(List<&2, Nat>, Pp.Cell.at(c), k, same) : {Pp.guarded(rest, pol) == Pp.keep.pick(Pp.Cls.guarded(Pp.class_of(pol, _)), c, Pp.guarded(rest, pol)) : List<&2, Pp.Cell>}
      %Equal.sym(Bool, Pp.Cls.guarded(Pp.class_of(pol, k)), False{}, hk) : {Pp.guarded(rest, pol) == Pp.keep.pick(_, c, Pp.guarded(rest, pol)) : List<&2, Pp.Cell>}
      {==}
    case False{}:
      %Equal.sym(List<&2, Pp.Cell>, Pp.guarded(Pp.set(rest, k, v), pol), Pp.guarded(rest, pol), ih) : {Pp.keep.pick(Pp.Cls.guarded(Pp.class_of(pol, Pp.Cell.at(c))), c, _) == Pp.guarded(c <> rest, pol) : List<&2, Pp.Cell>}
      {==}

# a write at a location that is not guarded keeps every guarded cell
def pp.guarded_set(cs: List<&2, Pp.Cell>, +pol: Pp.Pol, +k: List<&2, Nat>, +v: Nat, +hk: {Pp.Cls.guarded(Pp.class_of(pol, k)) == False{} : Bool}) -> {Pp.guarded(Pp.set(cs, k, v), pol) == Pp.guarded(cs, pol) : List<&2, Pp.Cell>}:
  match cs:
    case Nil{}:
      %Equal.sym(Bool, Pp.Cls.guarded(Pp.class_of(pol, k)), False{}, hk) : {Pp.keep.pick(_, Pp.Cell{k, v}, Nil{}) == Nil{} : List<&2, Pp.Cell>}
      {==}
    case +c <> +rest:
      pp.set_pick(Tl.ids.eq(Pp.Cell.at(c), k), c, rest, pol, k, v, {==}, hk, pp.guarded_set(rest, pol, k, v, hk))

# one write, by the gate's verdict b
def pp.put_keep(b: Bool, +pol: Pp.Pol, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, cs: List<&2, Pp.Cell>, +segs: List<&2, Tl.Seg>, +v: Nat, +ans: Pp.Ans, e: {Pp.runs(Pp.class(pol, ls, segs), Pp.Wr{}, auto, ans) == b : Bool}, no: {Pp.Ans.yes(ans) == False{} : Bool}) -> {Pp.guarded(Pp.put.pick(b, cs, Pp.Res.at(Pp.real(ls, segs)), v), pol) == Pp.guarded(cs, pol) : List<&2, Pp.Cell>}:
  match b:
    case True{}:
      +inside = LA.pp.gate_write_auto_only_inside(Pp.class(pol, ls, segs), auto, ans, e, no)
      pp.guarded_set(cs, pol, Pp.Res.at(Pp.real(ls, segs)), v, pp.inside_res(pol, Pp.real(ls, segs), inside))
    case False{}:
      {==}

def pp.config_needs_yes(es: List<&2, Pp.Put>, +pol: Pp.Pol, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, +cs: List<&2, Pp.Cell>, +no: {Pp.any_yes(es) == False{} : Bool}) -> {Pp.guarded(Pp.run(es, pol, ls, auto, cs), pol) == Pp.guarded(cs, pol) : List<&2, Pp.Cell>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Pp.Put{+segs, +v, +ans}:
          +na = pp.or_false_l(Pp.Ans.yes(ans), Pp.any_yes(rest), no)
          +nr = pp.or_false_r(Pp.Ans.yes(ans), Pp.any_yes(rest), no)
          +next = Pp.step(pol, ls, auto, cs, Pp.Put{segs, v, ans})
          Equal.trans(List<&2, Pp.Cell>, Pp.guarded(Pp.run(rest, pol, ls, auto, next), pol), Pp.guarded(next, pol), Pp.guarded(cs, pol), pp.config_needs_yes(rest, pol, ls, auto, next, nr), pp.put_keep(Pp.runs(Pp.class(pol, ls, segs), Pp.Wr{}, auto, ans), pol, ls, auto, cs, segs, v, ans, {==}, na))

def PathPolicy.config_needs_yes(es, pol, ls, auto, cs, no):
  pp.config_needs_yes(es, pol, ls, auto, cs, no)
