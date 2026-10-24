# eukhe: the proof of LAW color_near_spec
# The model's loop folds the distances left to right keeping the first
# strictly smaller one; the spec folds the same distances: a channel
# distance and a select per step (cn.absd, cn.sel), then induction.

import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color

def cn.absd.if(ge: Bool, +a: U32, +b: U32) -> {Co.sel(ge, (a - b : U32), (b - a : U32)) == Color.th.absd.if(ge, a, b) : U32}:
  match ge:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's channel distance is the spec's
def cn.absd(+a: U32, +b: U32) -> {Co.absdiff(a, b) == Color.th.absd(a, b) : U32}:
  cn.absd.if(U32.is_ge(a, b), a, b)

# the model's select is the spec's
def cn.sel(c: Bool, a: U32, b: U32) -> {Co.sel(c, a, b) == Color.th.pick(c, a, b) : U32}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def cn.go(+v: U32, xs: List<&2, U32>, +at: U32, +best: U32, +bestd: U32) -> {Co.near.go(v, xs, at, best, bestd) == Color.th.first_min(Color.th.dists(v, xs), at, best, bestd) : U32}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      +d = Co.absdiff(v, x)
      +c = U32.is_lt(d, bestd)
      %cn.absd(v, x) : {Co.near.go(v, t, (at + 1 : U32), Co.sel(c, at, best), Co.sel(c, d, bestd)) == Color.th.first_min(Color.th.dists(v, t), (at + 1 : U32), Color.th.pick(U32.is_lt(_, bestd), at, best), Color.th.pick(U32.is_lt(_, bestd), _, bestd)) : U32}
      %cn.sel(c, at, best) : {Co.near.go(v, t, (at + 1 : U32), Co.sel(c, at, best), Co.sel(c, d, bestd)) == Color.th.first_min(Color.th.dists(v, t), (at + 1 : U32), _, Color.th.pick(c, d, bestd)) : U32}
      %cn.sel(c, d, bestd) : {Co.near.go(v, t, (at + 1 : U32), Co.sel(c, at, best), Co.sel(c, d, bestd)) == Color.th.first_min(Color.th.dists(v, t), (at + 1 : U32), Co.sel(c, at, best), _) : U32}
      cn.go(v, t, (at + 1 : U32), Co.sel(c, at, best), Co.sel(c, d, bestd))

def Color.color_near_spec(v, xs):
  cn.go(v, xs, 0, 0, 4294967295)
