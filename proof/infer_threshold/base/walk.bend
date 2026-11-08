# eukhe: the cut of infer_threshold. The model walks the entries from the
# newest (M.walk: the tokens acc of the k entries kept so far, the best cut
# within the budget so far); the spec scans the cuts down from the largest
# (fit_spec), else up from the least (least_cut). The walk at k, its entries
# xs the ones after the k newest (iw.skip), is the spec once acc is held(k)
# and best the spec's scan up to k (iw.walk); past the budget every longer
# prefix is past it too (iw.over), and when no cut up to k fits there is no
# cut up to k at all (iw.nf).

import Base
import ../../../bend/infer_threshold.bend as M
import ../../../laws/infer_threshold.bend as IT
import ../../base/nat.bend as LNat

# Logic
# -----

def iw.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

def iw.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : iw.If(_, G)
  Unit{}

def iw.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  iw.tf(G, Equal.sym(Bool, False{}, True{}, e))

def iw.MIf(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is no Some
def iw.ns(-G: Type, -x: Nat, e: {None{} == Some{x} : Maybe<&2, Nat>}) -> G:
  %e : iw.MIf(_, G)
  Unit{}

def iw.and_t(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def iw.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def iw.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      iw.ft({b == True{} : Bool}, e)

def iw.or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Numbers
# -------

# (a + b) + c == (a + c) + b
def iw.rcomm(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  %LNat.add_assoc_r(a, c, b) : {Nat.add(Nat.add(a, b), c) == _ : Nat}
  %LNat.add_comm(b, c) : {Nat.add(Nat.add(a, b), c) == Nat.add(a, _) : Nat}
  LNat.add_assoc(a, b, c)

def iw.a1(+i: Nat) -> {Nat.add(i, 1n) == 1n+i : Nat}:
  %LNat.add_zero(i) : {Nat.add(i, 1n) == 1n+_ : Nat}
  LNat.add_succ(i, 0n)

# not a <= b: b <= a
def iw.nle(a: Nat, b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      iw.tf({Nat.is_le(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      iw.tf({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      iw.nle(p, q, h)

def iw.gt.at(v: Bool, +a: Nat, +x: Nat, +b: Nat, ev: {Nat.is_le(x, b) == v : Bool}, h: {Nat.is_le(a, b) == False{} : Bool}, ax: {Nat.is_le(a, x) == True{} : Bool}) -> {v == False{} : Bool}:
  match v:
    case True{}:
      Equal.trans(Bool, True{}, Nat.is_le(a, b), False{}, Equal.sym(Bool, Nat.is_le(a, b), True{}, LNat.pu.le_trans(a, x, b, ax, ev)), h)
    case False{}:
      {==}

# past b at a, past b at every x >= a
def iw.gt(+a: Nat, +x: Nat, +b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}, ax: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(x, b) == False{} : Bool}:
  iw.gt.at(Nat.is_le(x, b), a, x, b, {==}, h, ax)

# 1 + k <= n when k + (1 + l) == n
def iw.kn(+k: Nat, +l: Nat, -n: Nat, ek: {Nat.add(k, 1n+l) == n : Nat}) -> {Nat.is_le(1n+k, n) == True{} : Bool}:
  %ek : {Nat.is_le(1n+k, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(k, 1n+l), 1n+Nat.add(k, l), LNat.add_succ(k, l)) : {Nat.is_le(1n+k, _) == True{} : Bool}
  LNat.pu.le_add_r(k, l)

def iw.en(+k: Nat, +l: Nat, -n: Nat, ek: {Nat.add(k, 1n+l) == n : Nat}) -> {Nat.add(1n+k, l) == n : Nat}:
  Equal.trans(Nat, 1n+Nat.add(k, l), Nat.add(k, 1n+l), n, Equal.sym(Nat, Nat.add(k, 1n+l), 1n+Nat.add(k, l), LNat.add_succ(k, l)), ek)

def iw.en2(+k: Nat, +l: Nat, -n: Nat, ek: {Nat.add(k, 1n+l) == n : Nat}) -> {Nat.add(l, 1n+k) == n : Nat}:
  %ek : {Nat.add(l, 1n+k) == _ : Nat}
  %Equal.sym(Nat, Nat.add(k, 1n+l), 1n+Nat.add(k, l), LNat.add_succ(k, l)) : {Nat.add(l, 1n+k) == _ : Nat}
  %Equal.sym(Nat, Nat.add(l, 1n+k), 1n+Nat.add(l, k), LNat.add_succ(l, k)) : {_ == 1n+Nat.add(k, l) : Nat}
  %LNat.add_comm(l, k) : {1n+Nat.add(l, k) == 1n+_ : Nat}
  {==}

# The prefixes
# ------------

# the entries after the k newest
def iw.skip(k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      xs
    case 1n+j:
      match xs:
        case Nil{}:
          Nil{}
        case x <> rest:
          iw.skip(j, rest)

def iw.hd(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      x

def iw.tl(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      rest

def iw.skip_tl(k: Nat, all: List<&2, Nat>) -> {iw.skip(1n+k, all) == iw.tl(iw.skip(k, all)) : List<&2, Nat>}:
  match k:
    case 0n:
      match all:
        case Nil{}:
          {==}
        case y <> ys:
          {==}
    case 1n+j:
      match all:
        case Nil{}:
          {==}
        case y <> ys:
          iw.skip_tl(j, ys)

# the k + 1 newest hold the k newest and the next
def iw.held_step(k: Nat, all: List<&2, Nat>) -> {IT.held(1n+k, all) == Nat.add(IT.held(k, all), iw.hd(iw.skip(k, all))) : Nat}:
  match k:
    case 0n:
      match all:
        case Nil{}:
          {==}
        case y <> ys:
          {==}
    case 1n++j:
      match all:
        case Nil{}:
          {==}
        case +y <> +ys:
          %Equal.sym(Nat, IT.held(1n+j, ys), Nat.add(IT.held(j, ys), iw.hd(iw.skip(j, ys))), iw.held_step(j, ys)) : {Nat.add(_, y) == Nat.add(Nat.add(IT.held(j, ys), y), iw.hd(iw.skip(j, ys))) : Nat}
          iw.rcomm(IT.held(j, ys), iw.hd(iw.skip(j, ys)), y)

def iw.le_step(+m: Nat, +all: List<&2, Nat>) -> {Nat.is_le(IT.held(m, all), IT.held(1n+m, all)) == True{} : Bool}:
  %Equal.sym(Nat, IT.held(1n+m, all), Nat.add(IT.held(m, all), iw.hd(iw.skip(m, all))), iw.held_step(m, all)) : {Nat.is_le(IT.held(m, all), _) == True{} : Bool}
  LNat.pu.le_add_r(IT.held(m, all), iw.hd(iw.skip(m, all)))

# a longer prefix holds at least as much
def iw.mono(d: Nat, +all: List<&2, Nat>, +j: Nat) -> {Nat.is_le(IT.held(j, all), IT.held(Nat.add(d, j), all)) == True{} : Bool}:
  match d:
    case 0n:
      LNat.pu.le_refl(IT.held(j, all))
    case 1n++e:
      LNat.pu.le_trans(IT.held(j, all), IT.held(Nat.add(e, j), all), IT.held(1n+Nat.add(e, j), all), iw.mono(e, all, j), iw.le_step(Nat.add(e, j), all))

# acc + x == held(k + 1) when acc == held(k) and x is the next entry
def iw.acc(+k: Nat, +all: List<&2, Nat>, +acc: Nat, +x: Nat, -rest: List<&2, Nat>, es: {iw.skip(k, all) == x <> rest : List<&2, Nat>}, ea: {acc == IT.held(k, all) : Nat}) -> {Nat.add(acc, x) == IT.held(1n+k, all) : Nat}:
  %Equal.sym(Nat, IT.held(1n+k, all), Nat.add(IT.held(k, all), iw.hd(iw.skip(k, all))), iw.held_step(k, all)) : {Nat.add(acc, x) == _ : Nat}
  %Equal.sym(List<&2, Nat>, iw.skip(k, all), x <> rest, es) : {Nat.add(acc, x) == Nat.add(IT.held(k, all), iw.hd(_)) : Nat}
  %ea : {Nat.add(acc, x) == Nat.add(_, x) : Nat}
  {==}

def iw.es(+k: Nat, +all: List<&2, Nat>, -x: Nat, -rest: List<&2, Nat>, es: {iw.skip(k, all) == x <> rest : List<&2, Nat>}) -> {iw.skip(1n+k, all) == rest : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, iw.skip(1n+k, all), iw.tl(iw.skip(k, all)), iw.skip_tl(k, all)) : {_ == rest : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, iw.skip(k, all), x <> rest, es) : {iw.tl(_) == rest : List<&2, Nat>}
  {==}

# The cuts
# --------

def iw.or_at(a: Bool, b: Bool) -> {IT.mem.at(a, b) == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def iw.mem(cuts: List<&2, Nat>, +k: Nat) -> {IT.mem(cuts, k) == M.has(cuts, k) : Bool}:
  match cuts:
    case Nil{}:
      {==}
    case +c <> +rest:
      %iw.mem(rest, k) : {IT.mem.at(Nat.is_eq(c, k), IT.mem(rest, k)) == Bool.or(Nat.is_eq(c, k), _) : Bool}
      iw.or_at(Nat.is_eq(c, k), IT.mem(rest, k))

# 1 + k <= n is a cut of n entries when it is one of cuts
def iw.cut_has(+cuts: List<&2, Nat>, +n: Nat, +k: Nat, kn: {Nat.is_le(1n+k, n) == True{} : Bool}) -> {IT.is_cut(cuts, n, 1n+k) == M.has(cuts, 1n+k) : Bool}:
  %Equal.sym(Bool, Nat.is_le(1n+k, n), True{}, kn) : {Bool.and(Nat.is_lt(0n, 1n+k), Bool.and(_, IT.mem(cuts, 1n+k))) == M.has(cuts, 1n+k) : Bool}
  iw.mem(cuts, 1n+k)

def iw.wc(c: Bool, +k: Nat, best: Maybe<&2, Nat>) -> {M.walk.cut(c, k, best) == IT.fit_spec.at(c, k, best) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def iw.oe_none(y: Maybe<&2, Nat>) -> {IT.or_else(y, None{}) == y : Maybe<&2, Nat>}:
  match y:
    case None{}:
      {==}
    case Some{k}:
      {==}

# The scan up: k cuts, then d more
def iw.split.at(c: Bool, +s: Nat, -x: Maybe<&2, Nat>, -y: Maybe<&2, Nat>, -z: Maybe<&2, Nat>, ih: {x == IT.or_else(y, z) : Maybe<&2, Nat>}) -> {IT.fit_spec.at(c, s, x) == IT.or_else(IT.fit_spec.at(c, s, y), z) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      ih

def iw.split(k: Nat, +d: Nat, +cuts: List<&2, Nat>, +n: Nat, +s: Nat) -> {IT.least_cut(Nat.add(k, d), cuts, n, s) == IT.or_else(IT.least_cut(k, cuts, n, s), IT.least_cut(d, cuts, n, Nat.add(k, s))) : Maybe<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n++e:
      %LNat.add_succ(e, s) : {IT.least_cut(1n+Nat.add(e, d), cuts, n, s) == IT.or_else(IT.least_cut(1n+e, cuts, n, s), IT.least_cut(d, cuts, n, _)) : Maybe<&2, Nat>}
      iw.split.at(IT.is_cut(cuts, n, s), s, IT.least_cut(Nat.add(e, d), cuts, n, 1n+s), IT.least_cut(e, cuts, n, 1n+s), IT.least_cut(d, cuts, n, Nat.add(e, 1n+s)), iw.split(e, d, cuts, n, 1n+s))

def iw.lc_succ(+i: Nat, +cuts: List<&2, Nat>, +n: Nat) -> {IT.least_cut(1n+i, cuts, n, 1n) == IT.or_else(IT.least_cut(i, cuts, n, 1n), IT.least_cut(1n, cuts, n, 1n+i)) : Maybe<&2, Nat>}:
  %iw.a1(i) : {IT.least_cut(_, cuts, n, 1n) == IT.or_else(IT.least_cut(i, cuts, n, 1n), IT.least_cut(1n, cuts, n, _)) : Maybe<&2, Nat>}
  iw.split(i, 1n, cuts, n, 1n)

def iw.nf_step(c: Bool, +j: Nat, +x: Maybe<&2, Nat>, +y: Maybe<&2, Nat>, ih: {IT.or_else(x, y) == x : Maybe<&2, Nat>}) -> {IT.or_else(IT.fit_spec.at(c, j, x), IT.or_else(y, IT.fit_spec.at(c, j, None{}))) == IT.fit_spec.at(c, j, x) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Nat>, IT.or_else(y, None{}), y, iw.oe_none(y)) : {IT.or_else(x, _) == x : Maybe<&2, Nat>}
      ih

# within b up to k: no cut fits up to k only when there is no cut up to k
def iw.nf(k: Nat, +all: List<&2, Nat>, +cuts: List<&2, Nat>, +n: Nat, +b: Nat, +el: {Nat.is_le(IT.held(k, all), b) == True{} : Bool}) -> {IT.or_else(IT.fit_spec(all, cuts, n, b, k), IT.least_cut(k, cuts, n, 1n)) == IT.fit_spec(all, cuts, n, b, k) : Maybe<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n++i:
      %Equal.sym(Bool, Nat.is_le(IT.held(1n+i, all), b), True{}, el) : {IT.or_else(IT.fit_spec.at(Bool.and(IT.is_cut(cuts, n, 1n+i), _), 1n+i, IT.fit_spec(all, cuts, n, b, i)), IT.least_cut(1n+i, cuts, n, 1n)) == IT.fit_spec.at(Bool.and(IT.is_cut(cuts, n, 1n+i), _), 1n+i, IT.fit_spec(all, cuts, n, b, i)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Bool.and(IT.is_cut(cuts, n, 1n+i), True{}), IT.is_cut(cuts, n, 1n+i), iw.and_t(IT.is_cut(cuts, n, 1n+i))) : {IT.or_else(IT.fit_spec.at(_, 1n+i, IT.fit_spec(all, cuts, n, b, i)), IT.least_cut(1n+i, cuts, n, 1n)) == IT.fit_spec.at(_, 1n+i, IT.fit_spec(all, cuts, n, b, i)) : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, IT.least_cut(1n+i, cuts, n, 1n), IT.or_else(IT.least_cut(i, cuts, n, 1n), IT.least_cut(1n, cuts, n, 1n+i)), iw.lc_succ(i, cuts, n)) : {IT.or_else(IT.fit_spec.at(IT.is_cut(cuts, n, 1n+i), 1n+i, IT.fit_spec(all, cuts, n, b, i)), _) == IT.fit_spec.at(IT.is_cut(cuts, n, 1n+i), 1n+i, IT.fit_spec(all, cuts, n, b, i)) : Maybe<&2, Nat>}
      iw.nf_step(IT.is_cut(cuts, n, 1n+i), 1n+i, IT.fit_spec(all, cuts, n, b, i), IT.least_cut(i, cuts, n, 1n), iw.nf(i, all, cuts, n, b, LNat.pu.le_trans(IT.held(i, all), IT.held(1n+i, all), b, iw.le_step(i, all), el)))

# no cut fits up to k (best None): none is a cut
def iw.none_lc(+k: Nat, +all: List<&2, Nat>, +cuts: List<&2, Nat>, +n: Nat, +b: Nat, eb: {None{} == IT.fit_spec(all, cuts, n, b, k) : Maybe<&2, Nat>}, el: {Nat.is_le(IT.held(k, all), b) == True{} : Bool}) -> {None{} == IT.least_cut(k, cuts, n, 1n) : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, None{}, IT.fit_spec(all, cuts, n, b, k), eb) : {_ == IT.or_else(_, IT.least_cut(k, cuts, n, 1n)) : Maybe<&2, Nat>}
  Equal.sym(Maybe<&2, Nat>, IT.or_else(IT.fit_spec(all, cuts, n, b, k), IT.least_cut(k, cuts, n, 1n)), IT.fit_spec(all, cuts, n, b, k), iw.nf(k, all, cuts, n, b, el))

# past b at j: no longer prefix fits, the scan down skips it
def iw.over(d: Nat, +all: List<&2, Nat>, +cuts: List<&2, Nat>, +n: Nat, +b: Nat, +j: Nat, +h: {Nat.is_le(IT.held(j, all), b) == False{} : Bool}) -> {IT.fit_spec(all, cuts, n, b, Nat.add(d, j)) == IT.fit_spec(all, cuts, n, b, j) : Maybe<&2, Nat>}:
  match d:
    case 0n:
      {==}
    case 1n++e:
      %Equal.sym(Bool, Nat.is_le(IT.held(1n+Nat.add(e, j), all), b), False{}, iw.gt(IT.held(j, all), IT.held(1n+Nat.add(e, j), all), b, h, iw.mono(1n+e, all, j))) : {IT.fit_spec.at(Bool.and(IT.is_cut(cuts, n, 1n+Nat.add(e, j)), _), 1n+Nat.add(e, j), IT.fit_spec(all, cuts, n, b, Nat.add(e, j))) == IT.fit_spec(all, cuts, n, b, j) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Bool.and(IT.is_cut(cuts, n, 1n+Nat.add(e, j)), False{}), False{}, iw.and_f(IT.is_cut(cuts, n, 1n+Nat.add(e, j)))) : {IT.fit_spec.at(_, 1n+Nat.add(e, j), IT.fit_spec(all, cuts, n, b, Nat.add(e, j))) == IT.fit_spec(all, cuts, n, b, j) : Maybe<&2, Nat>}
      iw.over(e, all, cuts, n, b, j, h)

# The newest cut
# --------------

def iw.end(h: Bool, +k: Nat) -> {M.newest.end(h, k) == IT.fit_spec.at(h, k, None{}) : Maybe<&2, Nat>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# the newest cut from k (hit: k is a cut), xs the entries after the k newest
def iw.newest(xs: List<&2, Nat>, h: Bool, +cuts: List<&2, Nat>, +n: Nat, +k: Nat, +ek: {Nat.add(k, List.length(&2, Nat, xs)) == n : Nat}) -> {M.newest(xs, cuts, k, h) == IT.fit_spec.at(h, k, IT.least_cut(List.length(&2, Nat, xs), cuts, n, 1n+k)) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      iw.end(h, k)
    case x <> +rest:
      match h:
        case True{}:
          {==}
        case False{}:
          +e1 = iw.en(k, List.length(&2, Nat, rest), n, ek)
          %Equal.sym(Bool, IT.is_cut(cuts, n, 1n+k), M.has(cuts, 1n+k), iw.cut_has(cuts, n, k, iw.kn(k, List.length(&2, Nat, rest), n, ek))) : {M.newest(rest, cuts, 1n+k, M.has(cuts, 1n+k)) == IT.fit_spec.at(_, 1n+k, IT.least_cut(List.length(&2, Nat, rest), cuts, n, 2n+k)) : Maybe<&2, Nat>}
          iw.newest(rest, M.has(cuts, 1n+k), cuts, n, 1n+k, e1)

# The walk
# --------

def iw.walk.end(best: Maybe<&2, Nat>, +k: Nat, +all: List<&2, Nat>, +cuts: List<&2, Nat>, +n: Nat, +b: Nat, eb: {best == IT.fit_spec(all, cuts, n, b, k) : Maybe<&2, Nat>}, el: {Nat.is_le(IT.held(k, all), b) == True{} : Bool}) -> {best == IT.or_else(best, IT.least_cut(k, cuts, n, 1n)) : Maybe<&2, Nat>}:
  match best:
    case None{}:
      iw.none_lc(k, all, cuts, n, b, eb, el)
    case Some{j}:
      {==}

def iw.walk.nil(+cuts: List<&2, Nat>, +b: Nat, +acc: Nat, +k: Nat, +best: Maybe<&2, Nat>, +all: List<&2, Nat>, +n: Nat, ea: {acc == IT.held(k, all) : Nat}, +eb: {best == IT.fit_spec(all, cuts, n, b, k) : Maybe<&2, Nat>}, el: {Nat.is_le(acc, b) == True{} : Bool}, en: {Nat.add(k, 0n) == n : Nat}) -> {best == IT.or_else(IT.fit_spec(all, cuts, n, b, n), IT.least_cut(n, cuts, n, 1n)) : Maybe<&2, Nat>}:
  %Equal.trans(Nat, k, Nat.add(k, 0n), n, Equal.sym(Nat, Nat.add(k, 0n), k, LNat.add_zero(k)), en) : {best == IT.or_else(IT.fit_spec(all, cuts, n, b, _), IT.least_cut(_, cuts, n, 1n)) : Maybe<&2, Nat>}
  %eb : {best == IT.or_else(_, IT.least_cut(k, cuts, n, 1n)) : Maybe<&2, Nat>}
  +hk = Equal.trans(Bool, Nat.is_le(IT.held(k, all), b), Nat.is_le(acc, b), True{}, Equal.cong(Nat, Bool, h => Nat.is_le(h, b), IT.held(k, all), acc, Equal.sym(Nat, acc, IT.held(k, all), ea)), el)
  iw.walk.end(best, k, all, cuts, n, b, eb, hk)

def iw.walk.past(best: Maybe<&2, Nat>, +rest: List<&2, Nat>, +k: Nat, +all: List<&2, Nat>, +cuts: List<&2, Nat>, +n: Nat, +b: Nat, eb: {best == IT.fit_spec(all, cuts, n, b, k) : Maybe<&2, Nat>}, el: {Nat.is_le(IT.held(k, all), b) == True{} : Bool}, +en: {Nat.add(k, 1n+List.length(&2, Nat, rest)) == n : Nat}) -> {M.walk.over(best, rest, cuts, 1n+k) == IT.or_else(best, IT.least_cut(n, cuts, n, 1n)) : Maybe<&2, Nat>}:
  match best:
    case None{}:
      %en : {M.newest(rest, cuts, 1n+k, M.has(cuts, 1n+k)) == IT.least_cut(_, cuts, n, 1n) : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, IT.least_cut(Nat.add(k, 1n+List.length(&2, Nat, rest)), cuts, n, 1n), IT.or_else(IT.least_cut(k, cuts, n, 1n), IT.least_cut(1n+List.length(&2, Nat, rest), cuts, n, Nat.add(k, 1n))), iw.split(k, 1n+List.length(&2, Nat, rest), cuts, n, 1n)) : {M.newest(rest, cuts, 1n+k, M.has(cuts, 1n+k)) == _ : Maybe<&2, Nat>}
      %iw.none_lc(k, all, cuts, n, b, eb, el) : {M.newest(rest, cuts, 1n+k, M.has(cuts, 1n+k)) == IT.or_else(_, IT.least_cut(1n+List.length(&2, Nat, rest), cuts, n, Nat.add(k, 1n))) : Maybe<&2, Nat>}
      %Equal.sym(Nat, Nat.add(k, 1n), 1n+k, iw.a1(k)) : {M.newest(rest, cuts, 1n+k, M.has(cuts, 1n+k)) == IT.least_cut(1n+List.length(&2, Nat, rest), cuts, n, _) : Maybe<&2, Nat>}
      %Equal.sym(Bool, IT.is_cut(cuts, n, 1n+k), M.has(cuts, 1n+k), iw.cut_has(cuts, n, k, iw.kn(k, List.length(&2, Nat, rest), n, en))) : {M.newest(rest, cuts, 1n+k, M.has(cuts, 1n+k)) == IT.fit_spec.at(_, 1n+k, IT.least_cut(List.length(&2, Nat, rest), cuts, n, 2n+k)) : Maybe<&2, Nat>}
      iw.newest(rest, M.has(cuts, 1n+k), cuts, n, 1n+k, iw.en(k, List.length(&2, Nat, rest), n, en))
    case Some{j}:
      {==}

# the best cut after a step within b
def iw.walk.best(+k: Nat, +all: List<&2, Nat>, +cuts: List<&2, Nat>, +n: Nat, +b: Nat, +best: Maybe<&2, Nat>, eb: {best == IT.fit_spec(all, cuts, n, b, k) : Maybe<&2, Nat>}, hl: {Nat.is_le(IT.held(1n+k, all), b) == True{} : Bool}, kn: {Nat.is_le(1n+k, n) == True{} : Bool}) -> {M.walk.cut(M.has(cuts, 1n+k), 1n+k, best) == IT.fit_spec(all, cuts, n, b, 1n+k) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Nat.is_le(IT.held(1n+k, all), b), True{}, hl) : {M.walk.cut(M.has(cuts, 1n+k), 1n+k, best) == IT.fit_spec.at(Bool.and(IT.is_cut(cuts, n, 1n+k), _), 1n+k, IT.fit_spec(all, cuts, n, b, k)) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Bool.and(IT.is_cut(cuts, n, 1n+k), True{}), IT.is_cut(cuts, n, 1n+k), iw.and_t(IT.is_cut(cuts, n, 1n+k))) : {M.walk.cut(M.has(cuts, 1n+k), 1n+k, best) == IT.fit_spec.at(_, 1n+k, IT.fit_spec(all, cuts, n, b, k)) : Maybe<&2, Nat>}
  %Equal.sym(Bool, IT.is_cut(cuts, n, 1n+k), M.has(cuts, 1n+k), iw.cut_has(cuts, n, k, kn)) : {M.walk.cut(M.has(cuts, 1n+k), 1n+k, best) == IT.fit_spec.at(_, 1n+k, IT.fit_spec(all, cuts, n, b, k)) : Maybe<&2, Nat>}
  %eb : {M.walk.cut(M.has(cuts, 1n+k), 1n+k, best) == IT.fit_spec.at(M.has(cuts, 1n+k), 1n+k, _) : Maybe<&2, Nat>}
  iw.wc(M.has(cuts, 1n+k), 1n+k, best)

# the walk at k (acc held(k) <= b, best the scan down from k, xs the
# entries after the k newest) ends at the spec's cut
def iw.walk(xs: List<&2, Nat>, fits: Bool, +cuts: List<&2, Nat>, +b: Nat, +acc: Nat, +k: Nat, +best: Maybe<&2, Nat>, +all: List<&2, Nat>, +n: Nat,
  +ef: {M.walk.fits(xs, b, acc) == fits : Bool},
  +es: {iw.skip(k, all) == xs : List<&2, Nat>},
  +ea: {acc == IT.held(k, all) : Nat},
  +eb: {best == IT.fit_spec(all, cuts, n, b, k) : Maybe<&2, Nat>},
  el: {Nat.is_le(acc, b) == True{} : Bool},
  +en: {Nat.add(k, List.length(&2, Nat, xs)) == n : Nat})
  -> {M.walk(xs, cuts, b, acc, k, best, fits) == IT.or_else(IT.fit_spec(all, cuts, n, b, n), IT.least_cut(n, cuts, n, 1n)) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      iw.walk.nil(cuts, b, acc, k, best, all, n, ea, eb, el, en)
    case +x <> +rest:
      match fits:
        case True{}:
          +ea1 = iw.acc(k, all, acc, x, rest, es, ea)
          +hl = Equal.trans(Bool, Nat.is_le(IT.held(1n+k, all), b), Nat.is_le(Nat.add(acc, x), b), True{}, Equal.cong(Nat, Bool, h => Nat.is_le(h, b), IT.held(1n+k, all), Nat.add(acc, x), Equal.sym(Nat, Nat.add(acc, x), IT.held(1n+k, all), ea1)), ef)
          +eb1 = iw.walk.best(k, all, cuts, n, b, best, eb, hl, iw.kn(k, List.length(&2, Nat, rest), n, en))
          iw.walk(rest, M.walk.fits(rest, b, Nat.add(acc, x)), cuts, b, Nat.add(acc, x), 1n+k, M.walk.cut(M.has(cuts, 1n+k), 1n+k, best), all, n,
            {==}, iw.es(k, all, x, rest, es), ea1, eb1, ef, iw.en(k, List.length(&2, Nat, rest), n, en))
        case False{}:
          +ea1 = iw.acc(k, all, acc, x, rest, es, ea)
          +hf = Equal.trans(Bool, Nat.is_le(IT.held(1n+k, all), b), Nat.is_le(Nat.add(acc, x), b), False{}, Equal.cong(Nat, Bool, h => Nat.is_le(h, b), IT.held(1n+k, all), Nat.add(acc, x), Equal.sym(Nat, Nat.add(acc, x), IT.held(1n+k, all), ea1)), ef)
          +hk = Equal.trans(Bool, Nat.is_le(IT.held(k, all), b), Nat.is_le(acc, b), True{}, Equal.cong(Nat, Bool, h => Nat.is_le(h, b), IT.held(k, all), acc, Equal.sym(Nat, acc, IT.held(k, all), ea)), el)
          %iw.en2(k, List.length(&2, Nat, rest), n, en) : {M.walk.over(best, rest, cuts, 1n+k) == IT.or_else(IT.fit_spec(all, cuts, n, b, _), IT.least_cut(n, cuts, n, 1n)) : Maybe<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, IT.fit_spec(all, cuts, n, b, Nat.add(List.length(&2, Nat, rest), 1n+k)), IT.fit_spec(all, cuts, n, b, 1n+k), iw.over(List.length(&2, Nat, rest), all, cuts, n, b, 1n+k, hf)) : {M.walk.over(best, rest, cuts, 1n+k) == IT.or_else(_, IT.least_cut(n, cuts, n, 1n)) : Maybe<&2, Nat>}
          %Equal.sym(Bool, Nat.is_le(IT.held(1n+k, all), b), False{}, hf) : {M.walk.over(best, rest, cuts, 1n+k) == IT.or_else(IT.fit_spec.at(Bool.and(IT.is_cut(cuts, n, 1n+k), _), 1n+k, IT.fit_spec(all, cuts, n, b, k)), IT.least_cut(n, cuts, n, 1n)) : Maybe<&2, Nat>}
          %Equal.sym(Bool, Bool.and(IT.is_cut(cuts, n, 1n+k), False{}), False{}, iw.and_f(IT.is_cut(cuts, n, 1n+k))) : {M.walk.over(best, rest, cuts, 1n+k) == IT.or_else(IT.fit_spec.at(_, 1n+k, IT.fit_spec(all, cuts, n, b, k)), IT.least_cut(n, cuts, n, 1n)) : Maybe<&2, Nat>}
          %eb : {M.walk.over(best, rest, cuts, 1n+k) == IT.or_else(_, IT.least_cut(n, cuts, n, 1n)) : Maybe<&2, Nat>}
          iw.walk.past(best, rest, k, all, cuts, n, b, eb, hk, en)

# The cut
# -------

def iw.left.at(lt: Bool, +k: Nat) -> {M.cut.left.at(lt, k) == IT.fit_spec.at(lt, k, None{}) : Maybe<&2, Nat>}:
  match lt:
    case True{}:
      {==}
    case False{}:
      {==}

def iw.left(c: Maybe<&2, Nat>, +full: Nat) -> {M.cut.left(c, full) == IT.left_spec(c, full) : Maybe<&2, Nat>}:
  match c:
    case None{}:
      {==}
    case Some{+k}:
      iw.left.at(Nat.is_lt(k, full), k)

# the model's cut is the spec's
def iw.cut(+xs: List<&2, Nat>, +cuts: List<&2, Nat>, +b: Nat, +full: Nat) -> {M.cut(xs, cuts, b, full) == IT.cut_spec(xs, cuts, b, full) : Maybe<&2, Nat>}:
  +n = List.length(&2, Nat, xs)
  %Equal.sym(Maybe<&2, Nat>, M.walk(xs, cuts, b, 0n, 0n, None{}, M.walk.fits(xs, b, 0n)), IT.or_else(IT.fit_spec(xs, cuts, n, b, n), IT.least_cut(n, cuts, n, 1n)), iw.walk(xs, M.walk.fits(xs, b, 0n), cuts, b, 0n, 0n, None{}, xs, n, {==}, {==}, {==}, {==}, LNat.pu.le_zero(b), {==})) : {M.cut.left(_, full) == IT.left_spec(IT.or_else(IT.fit_spec(xs, cuts, n, b, n), IT.least_cut(n, cuts, n, 1n)), full) : Maybe<&2, Nat>}
  iw.left(IT.or_else(IT.fit_spec(xs, cuts, n, b, n), IT.least_cut(n, cuts, n, 1n)), full)
