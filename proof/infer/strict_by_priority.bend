# eukhe: the proof of LAW strict_by_priority

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ./base.bend as LA

def pi.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pi.nle_le(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      LA.pi.absurd({True{} == True{} : Bool}, h)
    case 0n 1n+q:
      LA.pi.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pi.nle_le(p, q, h)

# every tool of ys has a priority of at most p
def pi.below(ys: List<&2, If.Tool>, +p: Nat) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case +y <> rest:
      Bool.and(Nat.is_le(If.Tool.prio(y), p), pi.below(rest, p))

# priorities never rise along xs
def pi.sorted(xs: List<&2, If.Tool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> +rest:
      Bool.and(pi.below(rest, If.Tool.prio(x)), pi.sorted(rest))

def pi.below_mono(+ys: List<&2, If.Tool>, +p: Nat, +q: Nat, +b: {pi.below(ys, p) == True{} : Bool}, +le: {Nat.is_le(p, q) == True{} : Bool}) -> {pi.below(ys, q) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case y <> rest:
      +a = Nat.is_le(If.Tool.prio(y), p)
      pi.and_t(Nat.is_le(If.Tool.prio(y), q), pi.below(rest, q), LA.pi.le_trans(If.Tool.prio(y), p, q, LA.pi.and_l(a, pi.below(rest, p), b), le), pi.below_mono(rest, p, q, LA.pi.and_r(a, pi.below(rest, p), b), le))

# merging x <> xt and y <> yt, each under the bound P, stays under P,
# whatever the verdict c is
def pms.below_mg(+xt: List<&2, If.Tool>, +yt: List<&2, If.Tool>, +x: If.Tool, +y: If.Tool, c: Bool, +P: Nat,
  +bx: {pi.below(x <> xt, P) == True{} : Bool},
  +by: {pi.below(y <> yt, P) == True{} : Bool})
  -> {pi.below(If.tmerge.go(xt, yt, x, y, c), P) == True{} : Bool}:
  match xt yt c:
    case Nil{} Nil{} True{}:
      pi.and_t(Nat.is_le(If.Tool.prio(x), P), pi.below(y <> Nil{}, P), LA.pi.and_l(Nat.is_le(If.Tool.prio(x), P), pi.below(Nil{}, P), bx), by)
    case Nil{} Nil{} False{}:
      pi.and_t(Nat.is_le(If.Tool.prio(y), P), pi.below(x <> Nil{}, P), LA.pi.and_l(Nat.is_le(If.Tool.prio(y), P), pi.below(Nil{}, P), by), bx)
    case Nil{} +y2 <> +yt2 True{}:
      pi.and_t(Nat.is_le(If.Tool.prio(x), P), pi.below(y <> y2 <> yt2, P), LA.pi.and_l(Nat.is_le(If.Tool.prio(x), P), pi.below(Nil{}, P), bx), by)
    case Nil{} +y2 <> +yt2 False{}:
      +M = If.tmerge.go(Nil{}, yt2, x, y2, Nat.is_le(If.Tool.prio(y2), If.Tool.prio(x)))
      +a = Nat.is_le(If.Tool.prio(y), P)
      pi.and_t(a, pi.below(M, P), LA.pi.and_l(a, pi.below(y2 <> yt2, P), by),
        pms.below_mg(Nil{}, yt2, x, y2, Nat.is_le(If.Tool.prio(y2), If.Tool.prio(x)), P, bx, LA.pi.and_r(a, pi.below(y2 <> yt2, P), by)))
    case +x2 <> +xt2 Nil{} True{}:
      +M = If.tmerge.go(xt2, Nil{}, x2, y, Nat.is_le(If.Tool.prio(y), If.Tool.prio(x2)))
      +a = Nat.is_le(If.Tool.prio(x), P)
      pi.and_t(a, pi.below(M, P), LA.pi.and_l(a, pi.below(x2 <> xt2, P), bx),
        pms.below_mg(xt2, Nil{}, x2, y, Nat.is_le(If.Tool.prio(y), If.Tool.prio(x2)), P, LA.pi.and_r(a, pi.below(x2 <> xt2, P), bx), by))
    case +x2 <> +xt2 Nil{} False{}:
      pi.and_t(Nat.is_le(If.Tool.prio(y), P), pi.below(x <> x2 <> xt2, P), LA.pi.and_l(Nat.is_le(If.Tool.prio(y), P), pi.below(Nil{}, P), by), bx)
    case +x2 <> +xt2 +y2 <> +yt2 True{}:
      +M = If.tmerge.go(xt2, y2 <> yt2, x2, y, Nat.is_le(If.Tool.prio(y), If.Tool.prio(x2)))
      +a = Nat.is_le(If.Tool.prio(x), P)
      pi.and_t(a, pi.below(M, P), LA.pi.and_l(a, pi.below(x2 <> xt2, P), bx),
        pms.below_mg(xt2, y2 <> yt2, x2, y, Nat.is_le(If.Tool.prio(y), If.Tool.prio(x2)), P, LA.pi.and_r(a, pi.below(x2 <> xt2, P), bx), by))
    case +x2 <> +xt2 +y2 <> +yt2 False{}:
      +M = If.tmerge.go(x2 <> xt2, yt2, x, y2, Nat.is_le(If.Tool.prio(y2), If.Tool.prio(x)))
      +a = Nat.is_le(If.Tool.prio(y), P)
      pi.and_t(a, pi.below(M, P), LA.pi.and_l(a, pi.below(y2 <> yt2, P), by),
        pms.below_mg(x2 <> xt2, yt2, x, y2, Nat.is_le(If.Tool.prio(y2), If.Tool.prio(x)), P, bx, LA.pi.and_r(a, pi.below(y2 <> yt2, P), by)))

# merging the sorted x <> xt and y <> yt, with c the verdict
# Nat.is_le(prio y, prio x), gives a sorted list
def pms.sorted_mg(+xt: List<&2, If.Tool>, +yt: List<&2, If.Tool>, +x: If.Tool, +y: If.Tool, c: Bool,
  +eb: {Nat.is_le(If.Tool.prio(y), If.Tool.prio(x)) == c : Bool},
  +sx: {pi.sorted(x <> xt) == True{} : Bool},
  +sy: {pi.sorted(y <> yt) == True{} : Bool})
  -> {pi.sorted(If.tmerge.go(xt, yt, x, y, c)) == True{} : Bool}:
  match xt yt c:
    case Nil{} Nil{} True{}:
      +px = If.Tool.prio(x)
      +py = If.Tool.prio(y)
      pi.and_t(pi.below(y <> Nil{}, px), pi.sorted(y <> Nil{}), pi.and_t(Nat.is_le(py, px), pi.below(Nil{}, px), eb, {==}), sy)
    case Nil{} Nil{} False{}:
      +px = If.Tool.prio(x)
      +py = If.Tool.prio(y)
      +le = pi.nle_le(py, px, eb)
      pi.and_t(pi.below(x <> Nil{}, py), pi.sorted(x <> Nil{}), pi.and_t(Nat.is_le(px, py), pi.below(Nil{}, py), le, {==}), sx)
    case Nil{} +y2 <> +yt2 True{}:
      +px = If.Tool.prio(x)
      +py = If.Tool.prio(y)
      +Y = {y2 <> yt2 : List<&2, If.Tool>}
      pi.and_t(pi.below(y <> Y, px), pi.sorted(y <> Y),
        pi.and_t(Nat.is_le(py, px), pi.below(Y, px), eb, pi.below_mono(Y, py, px, LA.pi.and_l(pi.below(Y, py), pi.sorted(Y), sy), eb)),
        sy)
    case Nil{} +y2 <> +yt2 False{}:
      +px = If.Tool.prio(x)
      +py = If.Tool.prio(y)
      +Y = {y2 <> yt2 : List<&2, If.Tool>}
      +c2 = Nat.is_le(If.Tool.prio(y2), px)
      +M = If.tmerge.go(Nil{}, yt2, x, y2, c2)
      +le = pi.nle_le(py, px, eb)
      pi.and_t(pi.below(M, py), pi.sorted(M),
        pms.below_mg(Nil{}, yt2, x, y2, c2, py, pi.and_t(Nat.is_le(px, py), pi.below(Nil{}, py), le, {==}), LA.pi.and_l(pi.below(Y, py), pi.sorted(Y), sy)),
        pms.sorted_mg(Nil{}, yt2, x, y2, c2, {==}, sx, LA.pi.and_r(pi.below(Y, py), pi.sorted(Y), sy)))
    case +x2 <> +xt2 Nil{} True{}:
      +px = If.Tool.prio(x)
      +py = If.Tool.prio(y)
      +X = {x2 <> xt2 : List<&2, If.Tool>}
      +c2 = Nat.is_le(py, If.Tool.prio(x2))
      +M = If.tmerge.go(xt2, Nil{}, x2, y, c2)
      pi.and_t(pi.below(M, px), pi.sorted(M),
        pms.below_mg(xt2, Nil{}, x2, y, c2, px, LA.pi.and_l(pi.below(X, px), pi.sorted(X), sx), pi.and_t(Nat.is_le(py, px), pi.below(Nil{}, px), eb, {==})),
        pms.sorted_mg(xt2, Nil{}, x2, y, c2, {==}, LA.pi.and_r(pi.below(X, px), pi.sorted(X), sx), sy))
    case +x2 <> +xt2 Nil{} False{}:
      +px = If.Tool.prio(x)
      +py = If.Tool.prio(y)
      +X = {x2 <> xt2 : List<&2, If.Tool>}
      +le = pi.nle_le(py, px, eb)
      pi.and_t(pi.below(x <> X, py), pi.sorted(x <> X),
        pi.and_t(Nat.is_le(px, py), pi.below(X, py), le, pi.below_mono(X, px, py, LA.pi.and_l(pi.below(X, px), pi.sorted(X), sx), le)),
        sx)
    case +x2 <> +xt2 +y2 <> +yt2 True{}:
      +px = If.Tool.prio(x)
      +py = If.Tool.prio(y)
      +X = {x2 <> xt2 : List<&2, If.Tool>}
      +Y = {y2 <> yt2 : List<&2, If.Tool>}
      +c2 = Nat.is_le(py, If.Tool.prio(x2))
      +M = If.tmerge.go(xt2, Y, x2, y, c2)
      pi.and_t(pi.below(M, px), pi.sorted(M),
        pms.below_mg(xt2, Y, x2, y, c2, px, LA.pi.and_l(pi.below(X, px), pi.sorted(X), sx),
          pi.and_t(Nat.is_le(py, px), pi.below(Y, px), eb, pi.below_mono(Y, py, px, LA.pi.and_l(pi.below(Y, py), pi.sorted(Y), sy), eb))),
        pms.sorted_mg(xt2, Y, x2, y, c2, {==}, LA.pi.and_r(pi.below(X, px), pi.sorted(X), sx), sy))
    case +x2 <> +xt2 +y2 <> +yt2 False{}:
      +px = If.Tool.prio(x)
      +py = If.Tool.prio(y)
      +X = {x2 <> xt2 : List<&2, If.Tool>}
      +Y = {y2 <> yt2 : List<&2, If.Tool>}
      +c2 = Nat.is_le(If.Tool.prio(y2), px)
      +M = If.tmerge.go(X, yt2, x, y2, c2)
      +le = pi.nle_le(py, px, eb)
      pi.and_t(pi.below(M, py), pi.sorted(M),
        pms.below_mg(X, yt2, x, y2, c2, py,
          pi.and_t(Nat.is_le(px, py), pi.below(X, py), le, pi.below_mono(X, px, py, LA.pi.and_l(pi.below(X, px), pi.sorted(X), sx), le)),
          LA.pi.and_l(pi.below(Y, py), pi.sorted(Y), sy)),
        pms.sorted_mg(X, yt2, x, y2, c2, {==}, sx, LA.pi.and_r(pi.below(Y, py), pi.sorted(Y), sy)))

# merging two sorted lists gives a sorted list
def pms.sorted_merge(+xs: List<&2, If.Tool>, +ys: List<&2, If.Tool>,
  +sx: {pi.sorted(xs) == True{} : Bool}, +sy: {pi.sorted(ys) == True{} : Bool})
  -> {pi.sorted(If.tmerge(xs, ys)) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      sy
    case +x <> +xt Nil{}:
      sx
    case +x <> +xt +y <> +yt:
      pms.sorted_mg(xt, yt, x, y, Nat.is_le(If.Tool.prio(y), If.Tool.prio(x)), {==}, sx, sy)

# tsort sorts every tree
def pms.sorted_tsort(t: If.TTree) -> {pi.sorted(If.tsort(t)) == True{} : Bool}:
  match t:
    case If.TTip{}:
      {==}
    case If.TLeaf{+v}:
      {==}
    case If.TNode{+l, +r}:
      pms.sorted_merge(If.tsort(l), If.tsort(r), pms.sorted_tsort(l), pms.sorted_tsort(r))

# ranking sorts by priority
def pi.sorted_rank(+ts: List<&2, If.Tool>) -> {pi.sorted(If.rank(ts)) == True{} : Bool}:
  pms.sorted_tsort(If.tjoin(If.tbuild(ts, If.TEnd{}), If.TTip{}))

def pi.dom_nil(+ys: List<&2, If.Tool>) -> {If.dominates(Nil{}, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case y <> rest:
      pi.dom_nil(rest)

def pi.dom_cons(+h: If.Tool, +X: List<&2, If.Tool>, +Y: List<&2, If.Tool>, +d: {If.dominates(X, Y) == True{} : Bool}, +b: {pi.below(Y, If.Tool.prio(h)) == True{} : Bool}) -> {If.dominates(h <> X, Y) == True{} : Bool}:
  match Y:
    case Nil{}:
      {==}
    case y <> rest:
      +py = If.Tool.prio(y)
      +ph = If.Tool.prio(h)
      +le = LA.pi.and_l(Nat.is_le(py, ph), pi.below(rest, ph), b)
      +ag = LA.pi.and_l(If.all_ge(X, py), If.dominates(X, rest), d)
      pi.and_t(If.all_ge(h <> X, py), If.dominates(h <> X, rest), pi.and_t(Nat.is_le(py, ph), If.all_ge(X, py), le, ag), pi.dom_cons(h, X, rest, LA.pi.and_r(If.all_ge(X, py), If.dominates(X, rest), d), LA.pi.and_r(Nat.is_le(py, ph), pi.below(rest, ph), b)))

def pi.below_drop(+xs: List<&2, If.Tool>, +n: Nat, +p: Nat, +b: {pi.below(xs, p) == True{} : Bool}) -> {pi.below(List.drop(&2, If.Tool, xs, n), p) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      b
    case h <> t 1n+q:
      pi.below_drop(t, q, p, LA.pi.and_r(Nat.is_le(If.Tool.prio(h), p), pi.below(t, p), b))

# a sorted list's take dominates its drop
def pi.dom_split(+xs: List<&2, If.Tool>, +n: Nat, +s: {pi.sorted(xs) == True{} : Bool}) -> {If.dominates(List.take(&2, If.Tool, xs, n), List.drop(&2, If.Tool, xs, n)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      pi.dom_nil(h <> t)
    case h <> t 1n+q:
      +ph = If.Tool.prio(h)
      pi.dom_cons(h, List.take(&2, If.Tool, t, q), List.drop(&2, If.Tool, t, q), pi.dom_split(t, q, LA.pi.and_r(pi.below(t, ph), pi.sorted(t), s)), pi.below_drop(t, q, ph, LA.pi.and_l(pi.below(t, ph), pi.sorted(t), s)))

def pi.strict_by_priority(+cap: Nat, +ts: List<&2, If.Tool>) -> {If.dominates(Pair.fst(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts)), Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict(cap, ts))) == True{} : Bool}:
  pi.dom_split(If.rank(ts), cap, pi.sorted_rank(ts))

def Infer.strict_by_priority(cap, ts):
  pi.strict_by_priority(cap, ts)
