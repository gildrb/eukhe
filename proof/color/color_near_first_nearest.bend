# eukhe: the proof of LAW color_near_first_nearest
# near's loop keeps the first strictly smaller distance. Over the values
# before x, each strictly farther than x, the kept distance stays above
# x's (cnf.pre: one step per value, the kept distance either stays or
# becomes that value's); at x the loop takes x's index and distance; over
# the values after x, none closer, it keeps them (cnf.post). The loop
# starts from the distance 4294967295: when x is not below it, no value is
# strictly farther than x (so none stands before it, LCw.cw.lt_top), none
# after x is below 4294967295 either (LCw.cw.le_ntop), and the loop keeps
# its start, index 0, which is x's.

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./base/word.bend as LCw

def cnf.absd.if(ge: Bool, +a: U32, +b: U32) -> {Co.sel(ge, (a - b : U32), (b - a : U32)) == Color.th.absd.if(ge, a, b) : U32}:
  match ge:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's channel distance is the law's
def cnf.absd(+a: U32, +b: U32) -> {Co.absdiff(a, b) == Color.th.absd(a, b) : U32}:
  cnf.absd.if(U32.is_ge(a, b), a, b)

# rest when b is False
def cnf.nb(b: Bool, rest: Bool) -> Bool:
  match b:
    case True{}:
      False{}
    case False{}:
      rest

def cnf.nb_l(b: Bool, -rest: Bool, e: {cnf.nb(b, rest) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, False{}, True{}, e)
    case False{}:
      {==}

def cnf.nb_r(b: Bool, -rest: Bool, e: {cnf.nb(b, rest) == True{} : Bool}) -> {rest == True{} : Bool}:
  match b:
    case True{}:
      LCw.cw.ft({rest == True{} : Bool}, e)
    case False{}:
      e

# no value of ys is closer to v than the distance bd
def cnf.none(+v: U32, +bd: U32, ys: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case y <> t:
      cnf.nb(U32.is_lt(Color.th.absd(v, y), bd), cnf.none(v, bd, t))

# values at least as far as x: none is closer than x
def cnf.none_far(+v: U32, +x: U32, ys: List<&2, U32>, +h: {Color.th.as_far(v, x, ys) == True{} : Bool}) -> {cnf.none(v, Color.th.absd(v, x), ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      +hy = LCw.cw.and_l(U32.is_le(Color.th.absd(v, x), Color.th.absd(v, y)), Color.th.as_far(v, x, t), h)
      +ht = LCw.cw.and_r(U32.is_le(Color.th.absd(v, x), Color.th.absd(v, y)), Color.th.as_far(v, x, t), h)
      %Equal.sym(Bool, U32.is_lt(Color.th.absd(v, y), Color.th.absd(v, x)), False{}, LCw.cw.le_nlt(Color.th.absd(v, x), Color.th.absd(v, y), hy)) : {cnf.nb(_, cnf.none(v, Color.th.absd(v, x), t)) == True{} : Bool}
      cnf.none_far(v, x, t, ht)

# values at least as far as x, x not below the top distance: none is below
# the top distance
def cnf.none_top(+v: U32, +x: U32, ys: List<&2, U32>, +h: {Color.th.as_far(v, x, ys) == True{} : Bool}, +e0: {U32.is_lt(Color.th.absd(v, x), 4294967295) == False{} : Bool}) -> {cnf.none(v, 4294967295, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      +hy = LCw.cw.and_l(U32.is_le(Color.th.absd(v, x), Color.th.absd(v, y)), Color.th.as_far(v, x, t), h)
      +ht = LCw.cw.and_r(U32.is_le(Color.th.absd(v, x), Color.th.absd(v, y)), Color.th.as_far(v, x, t), h)
      %Equal.sym(Bool, U32.is_lt(Color.th.absd(v, y), 4294967295), False{}, LCw.cw.le_ntop(Color.th.absd(v, x), Color.th.absd(v, y), hy, e0)) : {cnf.nb(_, cnf.none(v, 4294967295, t)) == True{} : Bool}
      cnf.none_top(v, x, t, ht, e0)

# the loop over values none closer than the kept distance keeps its index
def cnf.post(+v: U32, ys: List<&2, U32>, +at: U32, +best: U32, +bd: U32, +h: {cnf.none(v, bd, ys) == True{} : Bool}) -> {Co.near.go(v, ys, at, best, bd) == best : U32}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      +hy = cnf.nb_l(U32.is_lt(Color.th.absd(v, y), bd), cnf.none(v, bd, t), h)
      +ht = cnf.nb_r(U32.is_lt(Color.th.absd(v, y), bd), cnf.none(v, bd, t), h)
      %Equal.sym(U32, Co.absdiff(v, y), Color.th.absd(v, y), cnf.absd(v, y)) : {Co.near.go(v, t, (at + 1 : U32), Co.sel(U32.is_lt(_, bd), at, best), Co.sel(U32.is_lt(_, bd), _, bd)) == best : U32}
      %Equal.sym(Bool, U32.is_lt(Color.th.absd(v, y), bd), False{}, hy) : {Co.near.go(v, t, (at + 1 : U32), Co.sel(_, at, best), Co.sel(_, Color.th.absd(v, y), bd)) == best : U32}
      cnf.post(v, t, (at + 1 : U32), best, bd, ht)

# one step of the loop, whichever way its test falls
def cnf.pick(c: Bool, -v: U32, -l: List<&2, U32>, -a1: U32, -at: U32, -best: U32, -dy: U32, -bd: U32, -r: U32, ihT: {Co.near.go(v, l, a1, at, dy) == r : U32}, ihF: {Co.near.go(v, l, a1, best, bd) == r : U32}) -> {Co.near.go(v, l, a1, Co.sel(c, at, best), Co.sel(c, dy, bd)) == r : U32}:
  match c:
    case True{}:
      ihT
    case False{}:
      ihF

# the loop over values strictly farther than x, then x, then values none
# closer than x, started with a kept distance above x's: the index of x
def cnf.pre(+v: U32, pre: List<&2, U32>, +x: U32, +post: List<&2, U32>, +at: U32, +best: U32, +bd: U32, +far: {Color.th.farther(v, x, pre) == True{} : Bool}, +rest: {cnf.none(v, Color.th.absd(v, x), post) == True{} : Bool}, +hb: {U32.is_lt(Color.th.absd(v, x), bd) == True{} : Bool}) -> {Co.near.go(v, List.append(&2, U32, pre, x <> post), at, best, bd) == Color.th.index(pre, at) : U32}:
  match pre:
    case Nil{}:
      %Equal.sym(U32, Co.absdiff(v, x), Color.th.absd(v, x), cnf.absd(v, x)) : {Co.near.go(v, post, (at + 1 : U32), Co.sel(U32.is_lt(_, bd), at, best), Co.sel(U32.is_lt(_, bd), _, bd)) == at : U32}
      %Equal.sym(Bool, U32.is_lt(Color.th.absd(v, x), bd), True{}, hb) : {Co.near.go(v, post, (at + 1 : U32), Co.sel(_, at, best), Co.sel(_, Color.th.absd(v, x), bd)) == at : U32}
      cnf.post(v, post, (at + 1 : U32), at, Color.th.absd(v, x), rest)
    case +y <> +t:
      +fy = LCw.cw.and_l(U32.is_lt(Color.th.absd(v, x), Color.th.absd(v, y)), Color.th.farther(v, x, t), far)
      +ft = LCw.cw.and_r(U32.is_lt(Color.th.absd(v, x), Color.th.absd(v, y)), Color.th.farther(v, x, t), far)
      %Equal.sym(U32, Co.absdiff(v, y), Color.th.absd(v, y), cnf.absd(v, y)) : {Co.near.go(v, List.append(&2, U32, t, x <> post), (at + 1 : U32), Co.sel(U32.is_lt(_, bd), at, best), Co.sel(U32.is_lt(_, bd), _, bd)) == Color.th.index(t, (at + 1 : U32)) : U32}
      cnf.pick(U32.is_lt(Color.th.absd(v, y), bd), v, List.append(&2, U32, t, x <> post), (at + 1 : U32), at, best, Color.th.absd(v, y), bd, Color.th.index(t, (at + 1 : U32)), cnf.pre(v, t, x, post, (at + 1 : U32), at, Color.th.absd(v, y), ft, rest, fy), cnf.pre(v, t, x, post, (at + 1 : U32), best, bd, ft, rest, hb))

# near from its start, by whether x is below the top distance
def cnf.top(b0: Bool, +v: U32, pre: List<&2, U32>, +x: U32, +post: List<&2, U32>, +e0: {U32.is_lt(Color.th.absd(v, x), 4294967295) == b0 : Bool}, +far: {Color.th.farther(v, x, pre) == True{} : Bool}, +rest: {Color.th.as_far(v, x, post) == True{} : Bool}) -> {Co.near(v, List.append(&2, U32, pre, x <> post)) == Color.th.index(pre, 0) : U32}:
  match b0:
    case True{}:
      cnf.pre(v, pre, x, post, 0, 0, 4294967295, far, cnf.none_far(v, x, post, rest), e0)
    case False{}:
      match pre:
        case Nil{}:
          %Equal.sym(U32, Co.absdiff(v, x), Color.th.absd(v, x), cnf.absd(v, x)) : {Co.near.go(v, post, 1, Co.sel(U32.is_lt(_, 4294967295), 0, 0), Co.sel(U32.is_lt(_, 4294967295), _, 4294967295)) == 0 : U32}
          %Equal.sym(Bool, U32.is_lt(Color.th.absd(v, x), 4294967295), False{}, e0) : {Co.near.go(v, post, 1, Co.sel(_, 0, 0), Co.sel(_, Color.th.absd(v, x), 4294967295)) == 0 : U32}
          cnf.post(v, post, 1, 0, 4294967295, cnf.none_top(v, x, post, rest, e0))
        case +y <> +t:
          LCw.cw.clash({Co.near(v, List.append(&2, U32, y <> t, x <> post)) == Color.th.index(y <> t, 0) : U32}, U32.is_lt(Color.th.absd(v, x), 4294967295), LCw.cw.lt_top(Color.th.absd(v, x), Color.th.absd(v, y), LCw.cw.and_l(U32.is_lt(Color.th.absd(v, x), Color.th.absd(v, y)), Color.th.farther(v, x, t), far)), e0)

def Color.color_near_first_nearest(v, pre, x, post, far, rest):
  cnf.top(U32.is_lt(Color.th.absd(v, x), 4294967295), v, pre, x, post, {==}, far, rest)
