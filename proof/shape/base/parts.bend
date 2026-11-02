# eukhe: more pieces' parts (laws/shape/match.bend R6): Same, Bound, Begin, End,
# a capture, an Ahead, the rounds of a Many; a split from no place; a
# Many's parts followed by more parts.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../base.bend as LA
import ./has.bend as LH
import ./fuel.bend as LU
import ./chars.bend as LQ
import ./split.bend as LP

# Lists
# -----

def shr.has_fits(-z: S.St, xs: List<&2, S.St>, +n: Nat, h: Shape.sp_has(z, xs), +hf: {LU.shu.fits(n, xs) == True{} : Bool}) -> {Nat.is_lt(Shape.sp_left(z), n) == True{} : Bool}:
  match xs:
    case Nil{}:
      match h:
    case +x <> +t:
      match h:
        case Inl{e}:
          %e : {Nat.is_lt(Shape.sp_left(_), n) == True{} : Bool}
          LU.shu.head(n, x, t, hf)
        case Inr{k}:
          shr.has_fits(z, t, n, k, LU.shu.tail(n, x, t, hf))

def shr.app_nil(-z: S.St, +xs: List<&2, S.St>, h: Shape.sp_has(z, List.append(&2, S.St, xs, Nil{}))) -> Shape.sp_has(z, xs):
  LH.shh.conv(z, List.append(&2, S.St, xs, Nil{}), xs, LA.shb.app_nil(xs), h)

def shr.moved_has.go(-y: S.St, +l: Nat, +x: S.St, -t: List<&2, S.St>, e: Shape.sp_has(y, Shape.sp_if(Nat.is_lt(Shape.sp_left(x), l), [x])) | Shape.sp_has(y, Shape.sp_moved(l, t)), ih: Shape.sp_has(y, Shape.sp_moved(l, t)) -> Shape.sp_has(y, t)) -> Shape.sp_has(y, x <> t):
  match e:
    case Inl{a}:
      Inl{LH.shh.single(y, x, LP.shp.if_has(Nat.is_lt(Shape.sp_left(x), l), [x], y, a))}
    case Inr{b}:
      Inr{ih(b)}

def shr.moved_has(-y: S.St, +l: Nat, xs: List<&2, S.St>, h: Shape.sp_has(y, Shape.sp_moved(l, xs))) -> Shape.sp_has(y, xs):
  match xs:
    case Nil{}:
      match h:
    case +x <> +t:
      shr.moved_has.go(y, l, x, t, LH.shh.app_split(y, Shape.sp_if(Nat.is_lt(Shape.sp_left(x), l), [x]), Shape.sp_moved(l, t), h), k => shr.moved_has(y, l, t, k))


def shr.moved_lt.go(-y: S.St, +l: Nat, +x: S.St, -t: List<&2, S.St>, e: Shape.sp_has(y, Shape.sp_if(Nat.is_lt(Shape.sp_left(x), l), [x])) | Shape.sp_has(y, Shape.sp_moved(l, t)), ih: Shape.sp_has(y, Shape.sp_moved(l, t)) -> {Nat.is_lt(Shape.sp_left(y), l) == True{} : Bool}) -> {Nat.is_lt(Shape.sp_left(y), l) == True{} : Bool}:
  match e:
    case Inl{+a}:
      +ex = {LH.shh.single(y, x, LP.shp.if_has(Nat.is_lt(Shape.sp_left(x), l), [x], y, a)) : {x == y : S.St}}
      %ex : {Nat.is_lt(Shape.sp_left(_), l) == True{} : Bool}
      LP.shp.if_t(Nat.is_lt(Shape.sp_left(x), l), [x], y, a)
    case Inr{b}:
      ih(b)

# a round kept by Many has fewer chars after it than l
def shr.moved_lt(-y: S.St, +l: Nat, xs: List<&2, S.St>, h: Shape.sp_has(y, Shape.sp_moved(l, xs))) -> {Nat.is_lt(Shape.sp_left(y), l) == True{} : Bool}:
  match xs:
    case Nil{}:
      match h:
    case +x <> +t:
      shr.moved_lt.go(y, l, x, t, LH.shh.app_split(y, Shape.sp_if(Nat.is_lt(Shape.sp_left(x), l), [x]), Shape.sp_moved(l, t), h), k => shr.moved_lt(y, l, t, k))

# a reading with fewer chars after it than l is kept by Many
def shr.moved_in(+y: S.St, +l: Nat, xs: List<&2, S.St>, h: Shape.sp_has(y, xs), +hl: {Nat.is_lt(Shape.sp_left(y), l) == True{} : Bool}) -> Shape.sp_has(y, Shape.sp_moved(l, xs)):
  match xs:
    case Nil{}:
      match h:
    case +x <> +t:
      match h:
        case Inl{e}:
          %Equal.sym(S.St, x, y, e) : Shape.sp_has(y, List.append(&2, S.St, Shape.sp_if(Nat.is_lt(Shape.sp_left(_), l), [_]), Shape.sp_moved(l, t)))
          %Equal.sym(List<&2, S.St>, Shape.sp_if(Nat.is_lt(Shape.sp_left(y), l), [y]), [y], LP.shp.if_true(Nat.is_lt(Shape.sp_left(y), l), [y], hl)) : Shape.sp_has(y, List.append(&2, S.St, _, Shape.sp_moved(l, t)))
          Inl{{==}}
        case Inr{k}:
          LH.shh.app_r(y, Shape.sp_if(Nat.is_lt(Shape.sp_left(x), l), [x]), Shape.sp_moved(l, t), shr.moved_in(y, l, t, k, hl))

# Captures
# --------

def shr.cap_split(c: S.St, +t: List<&2, S.St>, +k: Nat, +at: Nat, +from: String) -> {Shape.sp_cap(c <> t, k, at, from) == List.append(&2, S.St, Shape.sp_cap([c], k, at, from), Shape.sp_cap(t, k, at, from)) : List<&2, S.St>}:
  match c:
    case S.St{pos, left, word, rest, caps}:
      {==}

def shr.cap_cons(+x: S.St, +t: List<&2, S.St>, +k: Nat, +at: Nat, +from: String, -z: S.St, h: Shape.sp_has(z, Shape.sp_cap(x <> t, k, at, from))) -> Shape.sp_has(z, List.append(&2, S.St, Shape.sp_cap([x], k, at, from), Shape.sp_cap(t, k, at, from))):
  LH.shh.conv(z, Shape.sp_cap(x <> t, k, at, from), List.append(&2, S.St, Shape.sp_cap([x], k, at, from), Shape.sp_cap(t, k, at, from)), shr.cap_split(x, t, k, at, from), h)

def shr.cap1(x: S.St, +k: Nat, +at: Nat, +from: String, -z: S.St, h: Shape.sp_has(z, Shape.sp_cap([x], k, at, from))) -> {Shape.sp_head(Shape.sp_cap([x], k, at, from)) == Some{z} : Maybe<&2, S.St>}:
  match x:
    case S.St{+pos, left, word, rest, caps}:
      +y = {S.St{pos, left, word, rest, List.set(&2, Maybe<&2, S.Got>, caps, k, Some{S.Got{at, pos, from}})} : S.St}
      Equal.cong(S.St, Maybe<&2, S.St>, w => Some{w}, y, z, LH.shh.single(z, y, h))

def shr.cap_conv(-c: S.St, -x: S.St, -k: Nat, -at: Nat, -from: String, -z: S.St, q: {c == x : S.St}, e: {Shape.sp_head(Shape.sp_cap([x], k, at, from)) == Some{z} : Maybe<&2, S.St>}) -> {Shape.sp_head(Shape.sp_cap([c], k, at, from)) == Some{z} : Maybe<&2, S.St>}:
  %Equal.sym(S.St, c, x, q) : {Shape.sp_head(Shape.sp_cap([_], k, at, from)) == Some{z} : Maybe<&2, S.St>}
  e

def shr.cap_from.fin(-x: S.St, -t: List<&2, S.St>, -k: Nat, -at: Nat, -from: String, -z: S.St, w: &y: S.St -> (Shape.sp_has(y, t) & {Shape.sp_head(Shape.sp_cap([y], k, at, from)) == Some{z} : Maybe<&2, S.St>})) -> &y: S.St -> (Shape.sp_has(y, x <> t) & {Shape.sp_head(Shape.sp_cap([y], k, at, from)) == Some{z} : Maybe<&2, S.St>}):
  (y, p) = w
  (hy, e) = p
  (y, (Inr{hy}, e))

def shr.cap_from.go(+x: S.St, -t: List<&2, S.St>, +k: Nat, +at: Nat, +from: String, -z: S.St, e: Shape.sp_has(z, Shape.sp_cap([x], k, at, from)) | Shape.sp_has(z, Shape.sp_cap(t, k, at, from)), ih: Shape.sp_has(z, Shape.sp_cap(t, k, at, from)) -> &y: S.St -> (Shape.sp_has(y, t) & {Shape.sp_head(Shape.sp_cap([y], k, at, from)) == Some{z} : Maybe<&2, S.St>})) -> &y: S.St -> (Shape.sp_has(y, x <> t) & {Shape.sp_head(Shape.sp_cap([y], k, at, from)) == Some{z} : Maybe<&2, S.St>}):
  match e:
    case Inl{a}:
      (x, (Inl{{==}}, shr.cap1(x, k, at, from, z, a)))
    case Inr{b}:
      shr.cap_from.fin(x, t, k, at, from, z, ih(b))


# a captured reading comes from an inner reading
def shr.cap_from(-z: S.St, xs: List<&2, S.St>, +k: Nat, +at: Nat, +from: String, h: Shape.sp_has(z, Shape.sp_cap(xs, k, at, from))) -> &y: S.St -> (Shape.sp_has(y, xs) & {Shape.sp_head(Shape.sp_cap([y], k, at, from)) == Some{z} : Maybe<&2, S.St>}):
  match xs:
    case Nil{}:
      match h:
    case +x <> +t:
      shr.cap_from.go(x, t, k, at, from, z, LH.shh.app_split(z, Shape.sp_cap([x], k, at, from), Shape.sp_cap(t, k, at, from), shr.cap_cons(x, t, k, at, from, z, h)), q => shr.cap_from(z, t, k, at, from, q))

# an inner reading, captured, is a reading of the capture
def shr.cap_has(-x: S.St, -z: S.St, xs: List<&2, S.St>, +k: Nat, +at: Nat, +from: String, hx: Shape.sp_has(x, xs), +e: {Shape.sp_head(Shape.sp_cap([x], k, at, from)) == Some{z} : Maybe<&2, S.St>}) -> Shape.sp_has(z, Shape.sp_cap(xs, k, at, from)):
  match xs:
    case Nil{}:
      match hx:
    case +c <> +t:
      match hx:
        case Inl{q}:
          LH.shh.conv(z, List.append(&2, S.St, Shape.sp_cap([c], k, at, from), Shape.sp_cap(t, k, at, from)), Shape.sp_cap(c <> t, k, at, from), Equal.sym(List<&2, S.St>, Shape.sp_cap(c <> t, k, at, from), List.append(&2, S.St, Shape.sp_cap([c], k, at, from), Shape.sp_cap(t, k, at, from)), shr.cap_split(c, t, k, at, from)), LH.shh.app_l(z, Shape.sp_cap([c], k, at, from), Shape.sp_cap(t, k, at, from), LP.shp.head_has(Shape.sp_cap([c], k, at, from), z, shr.cap_conv(c, x, k, at, from, z, q, e))))
        case Inr{q}:
          LH.shh.conv(z, List.append(&2, S.St, Shape.sp_cap([c], k, at, from), Shape.sp_cap(t, k, at, from)), Shape.sp_cap(c <> t, k, at, from), Equal.sym(List<&2, S.St>, Shape.sp_cap(c <> t, k, at, from), List.append(&2, S.St, Shape.sp_cap([c], k, at, from), Shape.sp_cap(t, k, at, from)), shr.cap_split(c, t, k, at, from)), LH.shh.app_r(z, Shape.sp_cap([c], k, at, from), Shape.sp_cap(t, k, at, from), shr.cap_has(x, z, t, k, at, from, q, e)))

