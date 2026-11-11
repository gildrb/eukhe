# eukhe: lemmas the proofs of area bound share

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ../../laws/wire.bend as Wire

# Logic
# -----

def bnd.BD(b: Bool, A: Type, B: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      B

# True is not False: anything follows
def bnd.tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : bnd.BD(_, Unit, A)
  Unit{}

# False is not True: anything follows
def bnd.ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : bnd.BD(_, A, Unit)
  Unit{}

# a or False is False only when a is
def bnd.or_f(a: Bool, e: {Bool.or(a, False{}) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

# Nats
# ----

def bnd.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, bnd.add_zero(p))

def bnd.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), bnd.add_succ(p, b))

def bnd.add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), bnd.add_assoc(p, b, c))

def bnd.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, bnd.add_zero(b))
    case 1n++p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), bnd.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, b), Nat.add(b, p), bnd.add_comm(p, b))

def bnd.sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      {==}

def bnd.sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      bnd.sub_self(p)

def bnd.le0(b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n++q:
      {==}

def bnd.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      bnd.le_refl(p)

def bnd.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      bnd.le0(c)
    case 1n++p 0n c:
      bnd.ft({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n++p 1n++q 0n:
      bnd.ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n++p 1n++q 1n++r:
      bnd.le_trans(p, q, r, ab, bc)

def bnd.le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      bnd.le_succ(p)

# a - d is at most a
def bnd.sub_le(a: Nat, d: Nat) -> {Nat.is_le(Nat.sub(a, d), a) == True{} : Bool}:
  match a d:
    case 0n +d:
      {==}
    case 1n++p 0n:
      bnd.le_refl(p)
    case 1n++p 1n++q:
      bnd.le_trans(Nat.sub(p, q), p, 1n+p, bnd.sub_le(p, q), bnd.le_succ(p))

# a + (b - a) is b when a is at most b
def bnd.add_sub(a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n +b:
      bnd.sub_zero(b)
    case 1n++p 0n:
      bnd.ft({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, h)
    case 1n++p 1n++q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.sub(q, p)), q, bnd.add_sub(p, q, h))

# (b - a) + a is b when a is at most b
def bnd.sub_add(a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(Nat.sub(b, a), a) == b : Nat}:
  match a b:
    case 0n +b:
      %Equal.sym(Nat, Nat.sub(b, 0n), b, bnd.sub_zero(b)) : {Nat.add(_, 0n) == b : Nat}
      bnd.add_zero(b)
    case 1n++p 0n:
      bnd.ft({Nat.add(Nat.sub(0n, 1n+p), 1n+p) == 0n : Nat}, h)
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(Nat.sub(q, p), 1n+p), 1n+Nat.add(Nat.sub(q, p), p), bnd.add_succ(Nat.sub(q, p), p)) : {_ == 1n+q : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.sub(q, p), p), q, bnd.sub_add(p, q, h))

# x <= b and w <= b - x give x + w <= b
def bnd.le_add_sub(x: Nat, +w: Nat, +b: Nat, hx: {Nat.is_le(x, b) == True{} : Bool}, hw: {Nat.is_le(w, Nat.sub(b, x)) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, w), b) == True{} : Bool}:
  match x b:
    case 0n +b:
      %bnd.sub_zero(b) : {Nat.is_le(w, _) == True{} : Bool}
      hw
    case 1n++p 0n:
      bnd.ft({Nat.is_le(Nat.add(1n+p, w), 0n) == True{} : Bool}, hx)
    case 1n++p 1n++q:
      bnd.le_add_sub(p, w, q, hx, hw)

# x + t <= b gives x <= b and t <= b - x
def bnd.le_add_l(x: Nat, +t: Nat, +b: Nat, h: {Nat.is_le(Nat.add(x, t), b) == True{} : Bool}) -> {Nat.is_le(x, b) == True{} : Bool}:
  match x b:
    case 0n +b:
      bnd.le0(b)
    case 1n++p 0n:
      bnd.ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n++p 1n++q:
      bnd.le_add_l(p, t, q, h)

def bnd.le_add_r(x: Nat, +t: Nat, +b: Nat, h: {Nat.is_le(Nat.add(x, t), b) == True{} : Bool}) -> {Nat.is_le(t, Nat.sub(b, x)) == True{} : Bool}:
  match x b:
    case 0n +b:
      %Equal.sym(Nat, Nat.sub(b, 0n), b, bnd.sub_zero(b)) : {Nat.is_le(t, _) == True{} : Bool}
      h
    case 1n++p 0n:
      bnd.ft({Nat.is_le(t, Nat.sub(0n, 1n+p)) == True{} : Bool}, h)
    case 1n++p 1n++q:
      bnd.le_add_r(p, t, q, h)

# Lists
# -----

def bnd.total(xs: List<&2, Nat>) -> {Bd.total(xs) == Bound.bd_total(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      Equal.cong(Nat, Nat, n => Nat.add(x, n), Bd.total(rest), Bound.bd_total(rest), bnd.total(rest))

def bnd.app_one(a: List<&2, Nat>, +x: Nat, +acc: List<&2, Nat>) -> {List.append(&2, Nat, List.append(&2, Nat, a, [x]), acc) == List.append(&2, Nat, a, x <> acc) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, ys => h <> ys, List.append(&2, Nat, List.append(&2, Nat, t, [x]), acc), List.append(&2, Nat, t, x <> acc), bnd.app_one(t, x, acc))

def bnd.app_nil(a: List<&2, Nat>) -> {List.append(&2, Nat, a, Nil{}) == a : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, ys => h <> ys, List.append(&2, Nat, t, Nil{}), t, bnd.app_nil(t))

def bnd.rev_go(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {List.reverse.go(&2, Nat, xs, acc) == List.append(&2, Nat, Bound.bd_rev(xs), acc) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, Bound.bd_rev(rest), [x]), acc), List.append(&2, Nat, Bound.bd_rev(rest), x <> acc), bnd.app_one(Bound.bd_rev(rest), x, acc)) : {List.reverse.go(&2, Nat, rest, x <> acc) == _ : List<&2, Nat>}
      bnd.rev_go(rest, x <> acc)

# the library's reverse is the spec's
def bnd.rev(+xs: List<&2, Nat>) -> {List.reverse(&2, Nat, xs) == Bound.bd_rev(xs) : List<&2, Nat>}:
  %bnd.app_nil(Bound.bd_rev(xs)) : {List.reverse(&2, Nat, xs) == _ : List<&2, Nat>}
  bnd.rev_go(xs, Nil{})

def bnd.total_app(a: List<&2, Nat>, +ys: List<&2, Nat>) -> {Bound.bd_total(List.append(&2, Nat, a, ys)) == Nat.add(Bound.bd_total(a), Bound.bd_total(ys)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Nat, Nat.add(Nat.add(h, Bound.bd_total(t)), Bound.bd_total(ys)), Nat.add(h, Nat.add(Bound.bd_total(t), Bound.bd_total(ys))), bnd.add_assoc(h, Bound.bd_total(t), Bound.bd_total(ys))) : {Nat.add(h, Bound.bd_total(List.append(&2, Nat, t, ys))) == _ : Nat}
      Equal.cong(Nat, Nat, n => Nat.add(h, n), Bound.bd_total(List.append(&2, Nat, t, ys)), Nat.add(Bound.bd_total(t), Bound.bd_total(ys)), bnd.total_app(t, ys))

def bnd.len_app(a: List<&2, Nat>, +ys: List<&2, Nat>) -> {List.length(&2, Nat, List.append(&2, Nat, a, ys)) == Nat.add(List.length(&2, Nat, a), List.length(&2, Nat, ys)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Nat, List.append(&2, Nat, t, ys)), Nat.add(List.length(&2, Nat, t), List.length(&2, Nat, ys)), bnd.len_app(t, ys))

# the reverse holds the same bytes and lines
def bnd.total_rev(xs: List<&2, Nat>) -> {Bound.bd_total(Bound.bd_rev(xs)) == Bound.bd_total(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Nat, Bound.bd_total(List.append(&2, Nat, Bound.bd_rev(rest), [x])), Nat.add(Bound.bd_total(Bound.bd_rev(rest)), Nat.add(x, 0n)), bnd.total_app(Bound.bd_rev(rest), [x])) : {_ == Nat.add(x, Bound.bd_total(rest)) : Nat}
      %Equal.sym(Nat, Bound.bd_total(Bound.bd_rev(rest)), Bound.bd_total(rest), bnd.total_rev(rest)) : {Nat.add(_, Nat.add(x, 0n)) == Nat.add(x, Bound.bd_total(rest)) : Nat}
      %Equal.sym(Nat, Nat.add(x, 0n), x, bnd.add_zero(x)) : {Nat.add(Bound.bd_total(rest), _) == Nat.add(x, Bound.bd_total(rest)) : Nat}
      bnd.add_comm(Bound.bd_total(rest), x)

def bnd.len_rev(xs: List<&2, Nat>) -> {List.length(&2, Nat, Bound.bd_rev(xs)) == List.length(&2, Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Nat, List.length(&2, Nat, List.append(&2, Nat, Bound.bd_rev(rest), [x])), Nat.add(List.length(&2, Nat, Bound.bd_rev(rest)), 1n), bnd.len_app(Bound.bd_rev(rest), [x])) : {_ == 1n+List.length(&2, Nat, rest) : Nat}
      %Equal.sym(Nat, List.length(&2, Nat, Bound.bd_rev(rest)), List.length(&2, Nat, rest), bnd.len_rev(rest)) : {Nat.add(_, 1n) == 1n+List.length(&2, Nat, rest) : Nat}
      %Equal.sym(Nat, Nat.add(List.length(&2, Nat, rest), 1n), 1n+Nat.add(List.length(&2, Nat, rest), 0n), bnd.add_succ(List.length(&2, Nat, rest), 0n)) : {_ == 1n+List.length(&2, Nat, rest) : Nat}
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(List.length(&2, Nat, rest), 0n), List.length(&2, Nat, rest), bnd.add_zero(List.length(&2, Nat, rest)))

# The window
# ----------

# how many of the first lines of xs, at most k, fit within b bytes (the
# count a fill keeps)
def bnd.count_pick(fits: Bool, m: Nat) -> Nat:
  match fits:
    case True{}:
      1n+m
    case False{}:
      0n

def bnd.count(xs: List<&2, Nat>, k: Nat, +b: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +x <> rest:
      match k:
        case 0n:
          0n
        case 1n+j:
          bnd.count_pick(Nat.is_le(x, b), bnd.count(rest, j, Nat.sub(b, x)))

def bnd.fill_pick(fits: Bool, +x: Nat, +rest: List<&2, Nat>, +w: Bd.Win, +m: Nat, ih: {Bd.Win{Bound.bd_total(Bound.bd_take(rest, m)), m} == w : Bd.Win}) -> {Bd.Win{Bound.bd_total(Bound.bd_take(x <> rest, bnd.count_pick(fits, m))), bnd.count_pick(fits, m)} == Bd.fill.pick(fits, x, w) : Bd.Win}:
  match fits:
    case True{}:
      %ih : {Bd.Win{Nat.add(x, Bound.bd_total(Bound.bd_take(rest, m))), 1n+m} == Bd.fill.more(x, _) : Bd.Win}
      {==}
    case False{}:
      {==}

# the model's fill is the spec's first lines: the count of those that fit
def bnd.fill(xs: List<&2, Nat>, k: Nat, +b: Nat) -> {Bd.Win{Bound.bd_total(Bound.bd_take(xs, bnd.count(xs, k, b))), bnd.count(xs, k, b)} == Bd.fill(xs, k, b) : Bd.Win}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      match k:
        case 0n:
          {==}
        case 1n++j:
          bnd.fill_pick(Nat.is_le(x, b), x, rest, Bd.fill(rest, j, Nat.sub(b, x)), bnd.count(rest, j, Nat.sub(b, x)), bnd.fill(rest, j, Nat.sub(b, x)))

def bnd.lines(n: Nat, o: Bool) -> {Bd.lines(n, o) == Bound.bd_lines(n, o) : Nat}:
  match o:
    case False{}:
      {==}
    case True{}:
      {==}

# More Nats
# ---------

# not a < x gives x <= a
def bnd.nlt_le(a: Nat, x: Nat, e: {Nat.is_lt(a, x) == False{} : Bool}) -> {Nat.is_le(x, a) == True{} : Bool}:
  match a x:
    case a 0n:
      bnd.le0(a)
    case 0n 1n+q:
      bnd.tf({Nat.is_le(1n+q, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      bnd.nlt_le(p, q, e)

# not a <= x gives x <= a
def bnd.nle_le(a: Nat, x: Nat, e: {Nat.is_le(a, x) == False{} : Bool}) -> {Nat.is_le(x, a) == True{} : Bool}:
  match a x:
    case 0n 0n:
      bnd.tf({Nat.is_le(0n, 0n) == True{} : Bool}, e)
    case 0n 1n+q:
      bnd.tf({Nat.is_le(1n+q, 0n) == True{} : Bool}, e)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      bnd.nle_le(p, q, e)

# (1 + l) - s is 1 + (l - s) when s <= l
def bnd.sub_succ(l: Nat, s: Nat, h: {Nat.is_le(s, l) == True{} : Bool}) -> {Nat.sub(1n+l, s) == 1n+Nat.sub(l, s) : Nat}:
  match l s:
    case 0n 0n:
      {==}
    case 0n 1n+t:
      bnd.ft({Nat.sub(1n, 1n+t) == 1n+Nat.sub(0n, 1n+t) : Nat}, h)
    case 1n++p 0n:
      {==}
    case 1n++p 1n++t:
      bnd.sub_succ(p, t, h)

# a - (a - m) is m when m <= a
def bnd.sub_sub(a: Nat, m: Nat, h: {Nat.is_le(m, a) == True{} : Bool}) -> {Nat.sub(a, Nat.sub(a, m)) == m : Nat}:
  match a m:
    case 0n 0n:
      {==}
    case 0n 1n+t:
      bnd.ft({Nat.sub(0n, Nat.sub(0n, 1n+t)) == 1n+t : Nat}, h)
    case 1n++l 0n:
      bnd.sub_self(1n+l)
    case 1n++l 1n++t:
      %Equal.sym(Nat, Nat.sub(1n+l, Nat.sub(l, t)), 1n+Nat.sub(l, Nat.sub(l, t)), bnd.sub_succ(l, Nat.sub(l, t), bnd.sub_le(l, t))) : {_ == 1n+t : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(l, Nat.sub(l, t)), t, bnd.sub_sub(l, t, h))

# a - (a - m) is at most m
def bnd.subsub_le(a: Nat, m: Nat) -> {Nat.is_le(Nat.sub(a, Nat.sub(a, m)), m) == True{} : Bool}:
  match a m:
    case 0n m:
      bnd.le0(m)
    case 1n++p 0n:
      %Equal.sym(Nat, Nat.sub(p, p), 0n, bnd.sub_self(p)) : {Nat.is_le(_, 0n) == True{} : Bool}
      {==}
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.sub(1n+p, Nat.sub(p, q)), 1n+Nat.sub(p, Nat.sub(p, q)), bnd.sub_succ(p, Nat.sub(p, q), bnd.sub_le(p, q))) : {Nat.is_le(_, 1n+q) == True{} : Bool}
      bnd.subsub_le(p, q)

def bnd.least_le.at(le: Bool, +a: Nat, +x: Nat, e: {Nat.is_le(a, x) == le : Bool}) -> {Nat.is_le(Bd.least.pick(le, a, x), a) == True{} : Bool}:
  match le:
    case True{}:
      bnd.le_refl(a)
    case False{}:
      bnd.nle_le(a, x, e)

# the lesser of a and x is at most a
def bnd.least_le(+a: Nat, +x: Nat) -> {Nat.is_le(Bd.least(a, x), a) == True{} : Bool}:
  bnd.least_le.at(Nat.is_le(a, x), a, x, {==})

# The window within the text
# --------------------------

def bnd.le_add_mono(y: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(y, a), Nat.add(y, b)) == True{} : Bool}:
  match y:
    case 0n:
      h
    case 1n++p:
      bnd.le_add_mono(p, a, b, h)

def bnd.take_le(ys: List<&2, Nat>, n: Nat) -> {Nat.is_le(Bound.bd_total(Bound.bd_take(ys, n)), Bound.bd_total(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +r:
      match n:
        case 0n:
          bnd.le0(Bound.bd_total(y <> r))
        case 1n++p:
          bnd.le_add_mono(y, Bound.bd_total(Bound.bd_take(r, p)), Bound.bd_total(r), bnd.take_le(r, p))

def bnd.keep_bytes.of(m: Nat, +ys: List<&2, Nat>, c: Nat, hc: {Nat.is_le(c, Bound.bd_total(ys)) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_bytes(Bd.keep.of(Bd.Win{Bound.bd_total(Bound.bd_take(ys, m)), m}, ys, c)), Bound.bd_total(ys)) == True{} : Bool}:
  match m:
    case 0n:
      match ys:
        case Nil{}:
          {==}
        case +y <> +r:
          match c:
            case 0n:
              bnd.le0(Bound.bd_total(y <> r))
            case 1n++p:
              hc
    case 1n++p:
      bnd.take_le(ys, 1n+p)

# a keep under a cut within the lines keeps at most their bytes
def bnd.keep_bytes(+ys: List<&2, Nat>, k: Nat, b: Nat, +c: Nat, hc: {Nat.is_le(c, Bound.bd_total(ys)) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_bytes(Bd.keep(ys, k, b, c)), Bound.bd_total(ys)) == True{} : Bool}:
  match k:
    case 0n:
      bnd.le0(Bound.bd_total(ys))
    case 1n++j:
      match b:
        case 0n:
          bnd.le0(Bound.bd_total(ys))
        case 1n++q:
          %bnd.fill(ys, 1n+j, 1n+q) : {Nat.is_le(Bound.bd_win_bytes(Bd.keep.of(_, ys, c)), Bound.bd_total(ys)) == True{} : Bool}
          bnd.keep_bytes.of(bnd.count(ys, 1n+j, 1n+q), ys, c, hc)

def bnd.fill_lines.pick(fits: Bool, +x: Nat, w: Bd.Win, +n: Nat, ih: {Nat.is_le(Bound.bd_win_lines(w), n) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_lines(Bd.fill.pick(fits, x, w)), 1n+n) == True{} : Bool}:
  match fits:
    case True{}:
      match w:
        case Bd.Win{bb, l}:
          ih
    case False{}:
      bnd.le0(1n+n)

# a fill keeps at most the lines it has
def bnd.fill_lines(xs: List<&2, Nat>, k: Nat, +b: Nat) -> {Nat.is_le(Bound.bd_win_lines(Bd.fill(xs, k, b)), List.length(&2, Nat, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      match k:
        case 0n:
          bnd.le0(1n+List.length(&2, Nat, rest))
        case 1n++j:
          bnd.fill_lines.pick(Nat.is_le(x, b), x, Bd.fill(rest, j, Nat.sub(b, x)), List.length(&2, Nat, rest), bnd.fill_lines(rest, j, Nat.sub(b, x)))

def bnd.keep_lines.of(w: Bd.Win, xs: List<&2, Nat>, c: Nat, h: {Nat.is_le(Bound.bd_win_lines(w), List.length(&2, Nat, xs)) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_lines(Bd.keep.of(w, xs, c)), List.length(&2, Nat, xs)) == True{} : Bool}:
  match w:
    case Bd.Win{bb, l}:
      match l:
        case 0n:
          match xs:
            case Nil{}:
              {==}
            case +y <> +r:
              match c:
                case 0n:
                  bnd.le0(1n+List.length(&2, Nat, r))
                case 1n+p:
                  bnd.le0(List.length(&2, Nat, r))
        case 1n+m:
          h

# a keep keeps at most the lines it has
def bnd.keep_lines(+xs: List<&2, Nat>, k: Nat, b: Nat, +c: Nat) -> {Nat.is_le(Bound.bd_win_lines(Bd.keep(xs, k, b, c)), List.length(&2, Nat, xs)) == True{} : Bool}:
  match k:
    case 0n:
      bnd.le0(List.length(&2, Nat, xs))
    case 1n++j:
      match b:
        case 0n:
          bnd.le0(List.length(&2, Nat, xs))
        case 1n++q:
          bnd.keep_lines.of(Bd.fill(xs, 1n+j, 1n+q), xs, c, bnd.fill_lines(xs, 1n+j, 1n+q))

def bnd.tail_cut(+xs: List<&2, Nat>, +tl: Nat, tc: {Nat.is_le(tl, Bound.bd_total(xs)) == True{} : Bool}) -> {Nat.is_le(tl, Bound.bd_total(Bound.bd_rev(xs))) == True{} : Bool}:
  %Equal.sym(Nat, Bound.bd_total(Bound.bd_rev(xs)), Bound.bd_total(xs), bnd.total_rev(xs)) : {Nat.is_le(tl, _) == True{} : Bool}
  tc

def bnd.tail_bytes(+xs: List<&2, Nat>, +k: Nat, +b: Nat, +tl: Nat, tc: {Nat.is_le(tl, Bound.bd_total(xs)) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_bytes(Bd.keep(List.reverse(&2, Nat, xs), k, b, tl)), Bound.bd_total(xs)) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, List.reverse(&2, Nat, xs), Bound.bd_rev(xs), bnd.rev(xs)) : {Nat.is_le(Bound.bd_win_bytes(Bd.keep(_, k, b, tl)), Bound.bd_total(xs)) == True{} : Bool}
  %bnd.total_rev(xs) : {Nat.is_le(Bound.bd_win_bytes(Bd.keep(Bound.bd_rev(xs), k, b, tl)), _) == True{} : Bool}
  bnd.keep_bytes(Bound.bd_rev(xs), k, b, tl, bnd.tail_cut(xs, tl, tc))

def bnd.tail_lines(+xs: List<&2, Nat>, +k: Nat, +b: Nat, +tl: Nat) -> {Nat.is_le(Bound.bd_win_lines(Bd.keep(List.reverse(&2, Nat, xs), k, b, tl)), List.length(&2, Nat, xs)) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, List.reverse(&2, Nat, xs), Bound.bd_rev(xs), bnd.rev(xs)) : {Nat.is_le(Bound.bd_win_lines(Bd.keep(_, k, b, tl)), List.length(&2, Nat, xs)) == True{} : Bool}
  %bnd.len_rev(xs) : {Nat.is_le(Bound.bd_win_lines(Bd.keep(Bound.bd_rev(xs), k, b, tl)), _) == True{} : Bool}
  bnd.keep_lines(Bound.bd_rev(xs), k, b, tl)

# under cuts within the text, a window keeps at most the text's bytes
def bnd.win_bytes(c: Bd.Cap, x: Bd.Body, hc: {Nat.is_le(Bound.bd_body_head(x), Bound.bd_total(Bound.bd_body_lines(x))) == True{} : Bool}, tc: {Nat.is_le(Bound.bd_body_tail(x), Bound.bd_total(Bound.bd_body_lines(x))) == True{} : Bool}) -> {Nat.is_le(Bound.bd_win_bytes(Bd.window(c, x)), Bound.bd_total(Bound.bd_body_lines(x))) == True{} : Bool}:
  match c:
    case Bd.Cap{+b, +k, t}:
      match t:
        case False{}:
          match x:
            case Bd.Body{+xs, o, +h, +tl, m}:
              bnd.keep_bytes(xs, k, b, h, hc)
        case True{}:
          match x:
            case Bd.Body{+xs, o, +h, +tl, m}:
              bnd.tail_bytes(xs, k, b, tl, tc)

# a window keeps at most the text's lines
def bnd.win_lines(c: Bd.Cap, x: Bd.Body) -> {Nat.is_le(Bound.bd_win_lines(Bd.window(c, x)), List.length(&2, Nat, Bound.bd_body_lines(x))) == True{} : Bool}:
  match c:
    case Bd.Cap{+b, +k, t}:
      match t:
        case False{}:
          match x:
            case Bd.Body{+xs, o, +h, +tl, m}:
              bnd.keep_lines(xs, k, b, h)
        case True{}:
          match x:
            case Bd.Body{+xs, o, +h, +tl, m}:
              bnd.tail_lines(xs, k, b, tl)

# Replies
# -------

# a list that fits reads back whole (laws/wire.bend wire_list_round_trip,
# turned around to rewrite a decoded spelling into its list)
def bnd.read(+xs: List<&2, Nat>, h: {Bound.bd_fits(xs) == True{} : Bool}) -> {Wr.Got{xs, ""} == Wr.get_list(~Nat, ~Wr.get_nat, Bound.bd_spell(xs)) : Wr.Dec<List<&2, Nat>>}:
  Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, "")), Wr.Got{xs, ""}, Wire.wire_list_round_trip(xs, "", h))

# a Nat over 1 is no Bool
def bnd.bit_none(n: Nat, e: {Nat.is_le(n, 1n) == False{} : Bool}) -> {None{} == FBd.bit(n) : Maybe<&2, Bool>}:
  match n:
    case 0n:
      bnd.tf({None{} == FBd.bit(0n) : Maybe<&2, Bool>}, e)
    case 1n:
      bnd.tf({None{} == FBd.bit(1n) : Maybe<&2, Bool>}, e)
    case 2n+x:
      {==}

# a body whose shape is not a body's reads as none
def bnd.body_none(xs: List<&2, Nat>, e: {Bound.bd_body_ok(xs) == False{} : Bool}) -> {None{} == FBd.body(xs) : Maybe<&2, Bd.Body>}:
  match xs:
    case Nil{}:
      {==}
    case +o <> +a:
      match a:
        case Nil{}:
          {==}
        case +h <> +b:
          match b:
            case Nil{}:
              {==}
            case +t <> +c:
              match c:
                case Nil{}:
                  {==}
                case +m <> +ls:
                  %bnd.bit_none(o, e) : {None{} == FBd.body.of(_, h, t, m, ls) : Maybe<&2, Bd.Body>}
                  {==}

def bnd.least(le: Bool, a: Nat, b: Nat) -> {Bd.least.pick(le, a, b) == Bound.bd_least(le, a, b) : Nat}:
  match le:
    case True{}:
      {==}
    case False{}:
      {==}

def bnd.mline_go(more: Bool, +r: Nat, +rest: List<&2, Nat>, +p: Nat, +m: Maybe<&2, Nat>, ih: {m == Bound.bd_mline.go(more, rest, p) : Maybe<&2, Nat>}) -> {Bd.mline.add(r, m) == Bound.bd_mline.go(more, r <> rest, 1n+p) : Maybe<&2, Nat>}:
  match more:
    case True{}:
      %Equal.sym(Maybe<&2, Nat>, m, Bound.bd_mline.go(True{}, rest, p), ih) : {Bd.mline.add(r, _) == Some{Nat.add(Nat.add(r, Bound.bd_total(Bound.bd_take(rest, p))), 1n)} : Maybe<&2, Nat>}
      Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, Nat.add(r, Nat.add(Bound.bd_total(Bound.bd_take(rest, p)), 1n)), Nat.add(Nat.add(r, Bound.bd_total(Bound.bd_take(rest, p))), 1n), Equal.sym(Nat, Nat.add(Nat.add(r, Bound.bd_total(Bound.bd_take(rest, p))), 1n), Nat.add(r, Nat.add(Bound.bd_total(Bound.bd_take(rest, p)), 1n)), bnd.add_assoc(r, Bound.bd_total(Bound.bd_take(rest, p)), 1n)))
    case False{}:
      %Equal.sym(Maybe<&2, Nat>, m, Bound.bd_mline.go(False{}, rest, p), ih) : {Bd.mline.add(r, _) == None{} : Maybe<&2, Nat>}
      {==}

# the model's mline is the spec's
def bnd.mline(rs: List<&2, Nat>, +q: Nat) -> {Bd.mline(rs, q) == Bound.bd_mline(rs, q) : Maybe<&2, Nat>}:
  match rs:
    case Nil{}:
      match q:
        case 0n:
          {==}
        case 1n++p:
          {==}
    case +r <> +rest:
      match q:
        case 0n:
          {==}
        case 1n++p:
          bnd.mline_go(Nat.is_lt(p, List.length(&2, Nat, rest)), r, rest, p, Bd.mline(rest, p), bnd.mline(rest, p))

def bnd.mlines(m: Maybe<&2, Nat>, +len: Nat) -> {Bd.margin.lines(m, len) == Bound.bd_margin.lines(m, len) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

# the model's margin is the spec's
def bnd.margin(c: Bd.Cap, x: Bd.Body) -> {Bd.margin(c, x) == Bound.bd_margin(c, x) : Nat}:
  match c:
    case Bd.Cap{b, +k, t}:
      match x:
        case Bd.Body{+xs, +o, hc, tc, +mc}:
          %bnd.total(xs) : {Bd.least(mc, Bd.margin.lines(Bd.mline(List.reverse(&2, Nat, xs), Bd.lines(k, o)), Bd.total(xs))) == Bound.bd_margin.go(mc, Bound.bd_margin.lines(Bound.bd_mline(Bound.bd_rev(xs), Bound.bd_lines(k, o)), _)) : Nat}
          %bnd.lines(k, o) : {Bd.least(mc, Bd.margin.lines(Bd.mline(List.reverse(&2, Nat, xs), Bd.lines(k, o)), Bd.total(xs))) == Bound.bd_margin.go(mc, Bound.bd_margin.lines(Bound.bd_mline(Bound.bd_rev(xs), _), Bd.total(xs))) : Nat}
          %bnd.rev(xs) : {Bd.least(mc, Bd.margin.lines(Bd.mline(List.reverse(&2, Nat, xs), Bd.lines(k, o)), Bd.total(xs))) == Bound.bd_margin.go(mc, Bound.bd_margin.lines(Bound.bd_mline(_, Bd.lines(k, o)), Bd.total(xs))) : Nat}
          %bnd.mline(List.reverse(&2, Nat, xs), Bd.lines(k, o)) : {Bd.least(mc, Bd.margin.lines(Bd.mline(List.reverse(&2, Nat, xs), Bd.lines(k, o)), Bd.total(xs))) == Bound.bd_margin.go(mc, Bound.bd_margin.lines(_, Bd.total(xs))) : Nat}
          %bnd.mlines(Bd.mline(List.reverse(&2, Nat, xs), Bd.lines(k, o)), Bd.total(xs)) : {Bd.least(mc, Bd.margin.lines(Bd.mline(List.reverse(&2, Nat, xs), Bd.lines(k, o)), Bd.total(xs))) == Bound.bd_margin.go(mc, _) : Nat}
          bnd.least(Nat.is_le(mc, Bd.margin.lines(Bd.mline(List.reverse(&2, Nat, xs), Bd.lines(k, o)), Bd.total(xs))), mc, Bd.margin.lines(Bd.mline(List.reverse(&2, Nat, xs), Bd.lines(k, o)), Bd.total(xs)))

def bnd.fill_pick_orig(fits: Bool, +x: Nat, +rest: List<&2, Nat>, +w: Bd.Win, +m: Nat, ih: {Bd.Win{Bound.bd_total(Bound.bd_take(rest, m)), m} == w : Bd.Win}) -> {Bd.Win{Bound.bd_total(Bound.bd_take(x <> rest, Bound.bd_count.pick(fits, m))), Bound.bd_count.pick(fits, m)} == Bd.fill.pick(fits, x, w) : Bd.Win}:
  match fits:
    case True{}:
      %ih : {Bd.Win{Nat.add(x, Bound.bd_total(Bound.bd_take(rest, m))), 1n+m} == Bd.fill.more(x, _) : Bd.Win}
      {==}
    case False{}:
      {==}

# the model's fill is the spec's first lines: the count of those that fit
def bnd.fill_orig(xs: List<&2, Nat>, k: Nat, +b: Nat) -> {Bd.Win{Bound.bd_total(Bound.bd_take(xs, Bound.bd_count(xs, k, b))), Bound.bd_count(xs, k, b)} == Bd.fill(xs, k, b) : Bd.Win}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      match k:
        case 0n:
          {==}
        case 1n++j:
          bnd.fill_pick_orig(Nat.is_le(x, b), x, rest, Bd.fill(rest, j, Nat.sub(b, x)), Bound.bd_count(rest, j, Nat.sub(b, x)), bnd.fill_orig(rest, j, Nat.sub(b, x)))

def bnd.keep_none(xs: List<&2, Nat>, c: Nat) -> {Bd.keep.none(xs, c) == Bound.bd_keep.none(xs, c) : Bd.Win}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      match c:
        case 0n:
          {==}
        case 1n++p:
          {==}

def bnd.keep_of(m: Nat, +xs: List<&2, Nat>, +c: Nat) -> {Bd.keep.of(Bd.Win{Bound.bd_total(Bound.bd_take(xs, m)), m}, xs, c) == Bound.bd_keep.lines(m, xs, c) : Bd.Win}:
  match m:
    case 0n:
      bnd.keep_none(xs, c)
    case 1n++p:
      {==}

# the model's keep is the spec's
def bnd.keep(+xs: List<&2, Nat>, k: Nat, b: Nat, +c: Nat) -> {Bd.keep(xs, k, b, c) == Bound.bd_keep(xs, k, b, c) : Bd.Win}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      match b:
        case 0n:
          {==}
        case 1n++q:
          %bnd.fill_orig(xs, 1n+j, 1n+q) : {Bd.keep.of(_, xs, c) == Bound.bd_keep.lines(Bound.bd_count(xs, 1n+j, 1n+q), xs, c) : Bd.Win}
          bnd.keep_of(Bound.bd_count(xs, 1n+j, 1n+q), xs, c)

# the model's window is the spec's
def bnd.window(c: Bd.Cap, x: Bd.Body) -> {Bd.window(c, x) == Bound.bd_window(c, x) : Bd.Win}:
  match c:
    case Bd.Cap{+b, +k, t}:
      match t:
        case False{}:
          match x:
            case Bd.Body{+xs, o, +hc, +tc, mc}:
              bnd.keep(xs, k, b, hc)
        case True{}:
          match x:
            case Bd.Body{+xs, o, +hc, +tc, mc}:
              %Equal.sym(List<&2, Nat>, List.reverse(&2, Nat, xs), Bound.bd_rev(xs), bnd.rev(xs)) : {Bd.keep(_, k, b, tc) == Bound.bd_keep(Bound.bd_rev(xs), k, b, tc) : Bd.Win}
              bnd.keep(Bound.bd_rev(xs), k, b, tc)
