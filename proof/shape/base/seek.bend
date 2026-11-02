# eukhe: the matcher's first reading is the spec's (shk.seek): the
# frames a search keeps stand for the readings of what is still to read
# (shk.kd), every place's count of chars after it below the fuel F.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../base.bend as LA
import ./leaf.bend as LL
import ./all.bend as LAll
import ./has.bend as LH
import ./fuel.bend as LU
import ./first.bend as LF
import ./sound.bend as LS

# What the frames stand for
# -------------------------

# the readings X taken through the frames K, fuel F
def shk.kd(+F: Nat, K: S.Fr, X: List<&2, S.St>) -> List<&2, S.St>:
  match K:
    case S.FEnd{}:
      X
    case S.FSeq{t, b, k}:
      shk.kd(F, k, Shape.sp_reads(F, t, X, S.val(b)))
    case S.FCap{n, at, from, k}:
      shk.kd(F, k, Shape.sp_cap(X, n, at, from))
    case S.FRound{q, b, l, k}:
      shk.kd(F, k, Shape.sp_reads(F, S.many.next(q), Shape.sp_moved(l, X), S.val(b)))

# the first reading of the pieces ps from the places X (captures from B),
# then of the frames K, whose end condition holds
def shk.G(+F: Nat, K: S.Fr, +e: Bool, ps: List<&2, S.Piece>, +B: Nat, X: List<&2, S.St>) -> Maybe<&2, S.St>:
  Shape.sp_head(Shape.sp_keep(e, shk.kd(F, K, Shape.sp_reads(F, ps, X, B))))

def shk.or(x: Maybe<&2, S.St>, y: Maybe<&2, S.St>) -> Maybe<&2, S.St>:
  match x:
    case None{}:
      y
    case Some{r}:
      Some{r}

# the spec's answer to a call of the matcher
def shk.ans(+F: Nat, w: S.W, ps: List<&2, S.Piece>, b: S.Base, K: S.Fr, +e: Bool) -> Maybe<&2, S.St>:
  match w:
    case S.Want{s}:
      shk.G(F, K, e, ps, S.val(b), [s])
    case S.Have{r}:
      Some{r}
    case S.Nothing{}:
      None{}

# the place of w, as a list of none or one place
def shk.wl(w: S.W) -> List<&2, S.St>:
  match w:
    case S.Want{s}:
      [s]
    case S.Have{r}:
      Nil{}
    case S.Nothing{}:
      Nil{}

# Lists
# -----

def shk.app_nil_reads(f: Nat, ps: List<&2, S.Piece>, +B: Nat, +X: List<&2, S.St>) -> {List.append(&2, S.St, X, Shape.sp_reads(f, ps, Nil{}, B)) == X : List<&2, S.St>}:
  %Equal.sym(List<&2, S.St>, Shape.sp_reads(f, ps, Nil{}, B), Nil{}, LH.shh.reads_nil(f, ps, B)) : {List.append(&2, S.St, X, _) == X : List<&2, S.St>}
  LA.shb.app_nil(X)

def shk.cap_app(X: List<&2, S.St>, +Y: List<&2, S.St>, +n: Nat, +at: Nat, +from: String) -> {Shape.sp_cap(List.append(&2, S.St, X, Y), n, at, from) == List.append(&2, S.St, Shape.sp_cap(X, n, at, from), Shape.sp_cap(Y, n, at, from)) : List<&2, S.St>}:
  match X:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case S.St{+pos, +left, +word, +rest, +caps}:
          Equal.cong(List<&2, S.St>, List<&2, S.St>, r => S.St{pos, left, word, rest, List.set(&2, Maybe<&2, S.Got>, caps, n, Some{S.Got{at, pos, from}})} <> r, Shape.sp_cap(List.append(&2, S.St, t, Y), n, at, from), List.append(&2, S.St, Shape.sp_cap(t, n, at, from), Shape.sp_cap(Y, n, at, from)), shk.cap_app(t, Y, n, at, from))

def shk.moved_app(+l: Nat, X: List<&2, S.St>, +Y: List<&2, S.St>) -> {Shape.sp_moved(l, List.append(&2, S.St, X, Y)) == List.append(&2, S.St, Shape.sp_moved(l, X), Shape.sp_moved(l, Y)) : List<&2, S.St>}:
  match X:
    case Nil{}:
      {==}
    case +x <> +t:
      +a = {Shape.sp_if(Nat.is_lt(Shape.sp_left(x), l), [x]) : List<&2, S.St>}
      %Equal.sym(List<&2, S.St>, Shape.sp_moved(l, List.append(&2, S.St, t, Y)), List.append(&2, S.St, Shape.sp_moved(l, t), Shape.sp_moved(l, Y)), shk.moved_app(l, t, Y)) : {List.append(&2, S.St, a, _) == List.append(&2, S.St, List.append(&2, S.St, a, Shape.sp_moved(l, t)), Shape.sp_moved(l, Y)) : List<&2, S.St>}
      Equal.sym(List<&2, S.St>, List.append(&2, S.St, List.append(&2, S.St, a, Shape.sp_moved(l, t)), Shape.sp_moved(l, Y)), List.append(&2, S.St, a, List.append(&2, S.St, Shape.sp_moved(l, t), Shape.sp_moved(l, Y))), LA.shb.app_assoc(a, Shape.sp_moved(l, t), Shape.sp_moved(l, Y)))

def shk.kd_nil(+F: Nat, K: S.Fr) -> {shk.kd(F, K, Nil{}) == Nil{} : List<&2, S.St>}:
  match K:
    case S.FEnd{}:
      {==}
    case S.FSeq{+t, +b, +k}:
      %Equal.sym(List<&2, S.St>, Shape.sp_reads(F, t, Nil{}, S.val(b)), Nil{}, LH.shh.reads_nil(F, t, S.val(b))) : {shk.kd(F, k, _) == Nil{} : List<&2, S.St>}
      shk.kd_nil(F, k)
    case S.FCap{n, at, from, +k}:
      shk.kd_nil(F, k)
    case S.FRound{+q, +b, l, +k}:
      %Equal.sym(List<&2, S.St>, Shape.sp_reads(F, S.many.next(q), Nil{}, S.val(b)), Nil{}, LH.shh.reads_nil(F, S.many.next(q), S.val(b))) : {shk.kd(F, k, _) == Nil{} : List<&2, S.St>}
      shk.kd_nil(F, k)

def shk.kd_app(+F: Nat, K: S.Fr, +X: List<&2, S.St>, +Y: List<&2, S.St>) -> {shk.kd(F, K, List.append(&2, S.St, X, Y)) == List.append(&2, S.St, shk.kd(F, K, X), shk.kd(F, K, Y)) : List<&2, S.St>}:
  match K:
    case S.FEnd{}:
      {==}
    case S.FSeq{+t, +b, +k}:
      %Equal.sym(List<&2, S.St>, Shape.sp_reads(F, t, List.append(&2, S.St, X, Y), S.val(b)), List.append(&2, S.St, Shape.sp_reads(F, t, X, S.val(b)), Shape.sp_reads(F, t, Y, S.val(b))), LH.shh.reads_app(F, t, X, Y, S.val(b))) : {shk.kd(F, k, _) == List.append(&2, S.St, shk.kd(F, S.FSeq{t, b, k}, X), shk.kd(F, S.FSeq{t, b, k}, Y)) : List<&2, S.St>}
      shk.kd_app(F, k, Shape.sp_reads(F, t, X, S.val(b)), Shape.sp_reads(F, t, Y, S.val(b)))
    case S.FCap{+n, +at, +from, +k}:
      %Equal.sym(List<&2, S.St>, Shape.sp_cap(List.append(&2, S.St, X, Y), n, at, from), List.append(&2, S.St, Shape.sp_cap(X, n, at, from), Shape.sp_cap(Y, n, at, from)), shk.cap_app(X, Y, n, at, from)) : {shk.kd(F, k, _) == List.append(&2, S.St, shk.kd(F, S.FCap{n, at, from, k}, X), shk.kd(F, S.FCap{n, at, from, k}, Y)) : List<&2, S.St>}
      shk.kd_app(F, k, Shape.sp_cap(X, n, at, from), Shape.sp_cap(Y, n, at, from))
    case S.FRound{+q, +b, +l, +k}:
      %Equal.sym(List<&2, S.St>, Shape.sp_moved(l, List.append(&2, S.St, X, Y)), List.append(&2, S.St, Shape.sp_moved(l, X), Shape.sp_moved(l, Y)), shk.moved_app(l, X, Y)) : {shk.kd(F, k, Shape.sp_reads(F, S.many.next(q), _, S.val(b))) == List.append(&2, S.St, shk.kd(F, S.FRound{q, b, l, k}, X), shk.kd(F, S.FRound{q, b, l, k}, Y)) : List<&2, S.St>}
      %Equal.sym(List<&2, S.St>, Shape.sp_reads(F, S.many.next(q), List.append(&2, S.St, Shape.sp_moved(l, X), Shape.sp_moved(l, Y)), S.val(b)), List.append(&2, S.St, Shape.sp_reads(F, S.many.next(q), Shape.sp_moved(l, X), S.val(b)), Shape.sp_reads(F, S.many.next(q), Shape.sp_moved(l, Y), S.val(b))), LH.shh.reads_app(F, S.many.next(q), Shape.sp_moved(l, X), Shape.sp_moved(l, Y), S.val(b))) : {shk.kd(F, k, _) == List.append(&2, S.St, shk.kd(F, S.FRound{q, b, l, k}, X), shk.kd(F, S.FRound{q, b, l, k}, Y)) : List<&2, S.St>}
      shk.kd_app(F, k, Shape.sp_reads(F, S.many.next(q), Shape.sp_moved(l, X), S.val(b)), Shape.sp_reads(F, S.many.next(q), Shape.sp_moved(l, Y), S.val(b)))

def shk.head_app(X: List<&2, S.St>, Y: List<&2, S.St>) -> {Shape.sp_head(List.append(&2, S.St, X, Y)) == shk.or(Shape.sp_head(X), Shape.sp_head(Y)) : Maybe<&2, S.St>}:
  match X:
    case Nil{}:
      {==}
    case x <> t:
      {==}

def shk.G_app(+F: Nat, +K: S.Fr, +e: Bool, +ps: List<&2, S.Piece>, +B: Nat, +X: List<&2, S.St>, +Y: List<&2, S.St>) -> {shk.G(F, K, e, ps, B, List.append(&2, S.St, X, Y)) == shk.or(shk.G(F, K, e, ps, B, X), shk.G(F, K, e, ps, B, Y)) : Maybe<&2, S.St>}:
  +RX = {Shape.sp_reads(F, ps, X, B) : List<&2, S.St>}
  +RY = {Shape.sp_reads(F, ps, Y, B) : List<&2, S.St>}
  %Equal.sym(List<&2, S.St>, Shape.sp_reads(F, ps, List.append(&2, S.St, X, Y), B), List.append(&2, S.St, RX, RY), LH.shh.reads_app(F, ps, X, Y, B)) : {Shape.sp_head(Shape.sp_keep(e, shk.kd(F, K, _))) == shk.or(shk.G(F, K, e, ps, B, X), shk.G(F, K, e, ps, B, Y)) : Maybe<&2, S.St>}
  %Equal.sym(List<&2, S.St>, shk.kd(F, K, List.append(&2, S.St, RX, RY)), List.append(&2, S.St, shk.kd(F, K, RX), shk.kd(F, K, RY)), shk.kd_app(F, K, RX, RY)) : {Shape.sp_head(Shape.sp_keep(e, _)) == shk.or(shk.G(F, K, e, ps, B, X), shk.G(F, K, e, ps, B, Y)) : Maybe<&2, S.St>}
  %Equal.sym(List<&2, S.St>, Shape.sp_keep(e, List.append(&2, S.St, shk.kd(F, K, RX), shk.kd(F, K, RY))), List.append(&2, S.St, Shape.sp_keep(e, shk.kd(F, K, RX)), Shape.sp_keep(e, shk.kd(F, K, RY))), LA.shb.keep_app(e, shk.kd(F, K, RX), shk.kd(F, K, RY))) : {Shape.sp_head(_) == shk.or(shk.G(F, K, e, ps, B, X), shk.G(F, K, e, ps, B, Y)) : Maybe<&2, S.St>}
  shk.head_app(Shape.sp_keep(e, shk.kd(F, K, RX)), Shape.sp_keep(e, shk.kd(F, K, RY)))

def shk.keep_nil(e: Bool) -> {Shape.sp_head(Shape.sp_keep(e, Nil{})) == None{} : Maybe<&2, S.St>}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def shk.G_nil(+F: Nat, +K: S.Fr, +e: Bool, +ps: List<&2, S.Piece>, +B: Nat) -> {shk.G(F, K, e, ps, B, Nil{}) == None{} : Maybe<&2, S.St>}:
  %Equal.sym(List<&2, S.St>, Shape.sp_reads(F, ps, Nil{}, B), Nil{}, LH.shh.reads_nil(F, ps, B)) : {Shape.sp_head(Shape.sp_keep(e, shk.kd(F, K, _))) == None{} : Maybe<&2, S.St>}
  %Equal.sym(List<&2, S.St>, shk.kd(F, K, Nil{}), Nil{}, shk.kd_nil(F, K)) : {Shape.sp_head(Shape.sp_keep(e, _)) == None{} : Maybe<&2, S.St>}
  shk.keep_nil(e)

def shk.ans_want(+F: Nat, m: Maybe<&2, S.St>, +ps: List<&2, S.Piece>, +b: S.Base, +K: S.Fr, +e: Bool) -> {shk.ans(F, S.want(m), ps, b, K, e) == shk.G(F, K, e, ps, S.val(b), S.m2l(m)) : Maybe<&2, S.St>}:
  match m:
    case None{}:
      Equal.sym(Maybe<&2, S.St>, shk.G(F, K, e, ps, S.val(b), Nil{}), None{}, shk.G_nil(F, K, e, ps, S.val(b)))
    case Some{s}:
      {==}

def shk.ans_prefer(+F: Nat, x: Maybe<&2, S.St>, +m: Maybe<&2, S.St>, +ps: List<&2, S.Piece>, +b: S.Base, +K: S.Fr, +e: Bool) -> {shk.ans(F, S.prefer(x, m), ps, b, K, e) == shk.or(x, shk.G(F, K, e, ps, S.val(b), S.m2l(m))) : Maybe<&2, S.St>}:
  match x:
    case None{}:
      shk.ans_want(F, m, ps, b, K, e)
    case Some{r}:
      {==}

# Steps
# -----

# the readings of a piece list from one place, the rest (no places) none
def shk.G_tail(+F: Nat, +K: S.Fr, +e: Bool, +t: List<&2, S.Piece>, +B2: Nat, +R: List<&2, S.St>, ps: List<&2, S.Piece>, +B: Nat) -> {Shape.sp_head(Shape.sp_keep(e, shk.kd(F, K, List.append(&2, S.St, Shape.sp_reads(F, t, R, B2), Shape.sp_reads(F, ps, Nil{}, B))))) == shk.G(F, K, e, t, B2, R) : Maybe<&2, S.St>}:
  %Equal.sym(List<&2, S.St>, List.append(&2, S.St, Shape.sp_reads(F, t, R, B2), Shape.sp_reads(F, ps, Nil{}, B)), Shape.sp_reads(F, t, R, B2), shk.app_nil_reads(F, ps, B, Shape.sp_reads(F, t, R, B2))) : {Shape.sp_head(Shape.sp_keep(e, shk.kd(F, K, _))) == shk.G(F, K, e, t, B2, R) : Maybe<&2, S.St>}
  {==}

# a frame of pieces stands for their readings (none for no pieces)
def shk.push(+g: Nat, t: List<&2, S.Piece>, +c: S.Base, +K: S.Fr, +X: List<&2, S.St>) -> {shk.kd(1n+g, S.push(t, c, K), X) == shk.kd(1n+g, K, Shape.sp_reads(1n+g, t, X, S.val(c))) : List<&2, S.St>}:
  match t:
    case Nil{}:
      {==}
    case p <> u:
      {==}

def shk.G_push(+g: Nat, +t: List<&2, S.Piece>, +c: S.Base, +K: S.Fr, +e: Bool, +ps: List<&2, S.Piece>, +B: Nat, +X: List<&2, S.St>) -> {shk.G(1n+g, S.push(t, c, K), e, ps, B, X) == shk.G(1n+g, K, e, t, S.val(c), Shape.sp_reads(1n+g, ps, X, B)) : Maybe<&2, S.St>}:
  Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, z => Shape.sp_head(Shape.sp_keep(e, z)), shk.kd(1n+g, S.push(t, c, K), Shape.sp_reads(1n+g, ps, X, B)), shk.kd(1n+g, K, Shape.sp_reads(1n+g, t, Shape.sp_reads(1n+g, ps, X, B), S.val(c))), shk.push(g, t, c, K, Shape.sp_reads(1n+g, ps, X, B)))

# a place every piece and frame has read
def shk.done(e: Bool, s: S.St) -> {S.done(e, s) == Shape.sp_head(Shape.sp_keep(e, [s])) : Maybe<&2, S.St>}:
  match e:
    case False{}:
      {==}
    case True{}:
      match s:
        case S.St{pos, left, word, rest, caps}:
          match rest:
            case SNil{}:
              {==}
            case SCon{x, t}:
              {==}

def shk.keep1(b: Bool, x: S.St) -> {S.m2l(S.keep(b, x)) == List.append(&2, S.St, Shape.sp_if(b, [x]), Nil{}) : List<&2, S.St>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def shk.moved1(+l: Nat, s: S.St) -> {S.m2l(S.moved(l, s)) == Shape.sp_moved(l, [s]) : List<&2, S.St>}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      shk.keep1(Nat.is_lt(left, l), S.St{pos, left, word, rest, caps})

def shk.ahead1(neg: Bool, xs: List<&2, S.St>, s: S.St) -> {S.m2l(S.ahead.at(neg, Shape.sp_head(xs), s)) == Shape.sp_ahead(neg, xs, s) : List<&2, S.St>}:
  match neg:
    case True{}:
      match xs:
        case Nil{}:
          {==}
        case x <> t:
          {==}
    case False{}:
      match xs:
        case Nil{}:
          {==}
        case x <> t:
          {==}

def shk.many_next(i: List<&2, S.Piece>, min: Nat, t: List<&2, S.Piece>) -> {S.many.next(S.Many{i, min} <> t) == S.Many{i, Shape.sp_dec(min)} <> t : List<&2, S.Piece>}:
  match min:
    case 0n:
      {==}
    case 1n+k:
      {==}

def shk.run_next(c: S.Cls, min: Nat, max: Maybe<&2, Nat>, t: List<&2, S.Piece>) -> {S.run.next(min, max, c, t, S.Run{c, min, max} <> t) == S.Run{c, Shape.sp_dec(min), Shape.sp_less(max)} <> t : List<&2, S.Piece>}:
  match min:
    case 0n:
      match max:
        case None{}:
          {==}
        case Some{n}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              {==}
    case 1n+k:
      match max:
        case None{}:
          {==}
        case Some{n}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              {==}

# Many: the repetition then t from places Y, as the repetition's
# readings, then t
def shk.seq(+g: Nat, +i: List<&2, S.Piece>, +m: Nat, +t: List<&2, S.Piece>, Y: List<&2, S.St>, +B: Nat) -> {Shape.sp_reads(1n+g, S.Many{i, m} <> t, Y, B) == Shape.sp_reads(1n+g, t, Shape.sp_reads(1n+g, [S.Many{i, m}], Y, B), Nat.add(B, Shape.sp_ncaps(i))) : List<&2, S.St>}:
  match Y:
    case Nil{}:
      Equal.sym(List<&2, S.St>, Shape.sp_reads(1n+g, t, Nil{}, Nat.add(B, Shape.sp_ncaps(i))), Nil{}, LH.shh.reads_nil(1n+g, t, Nat.add(B, Shape.sp_ncaps(i))))
    case +y <> +rest:
      +A = {List.append(&2, S.St, Shape.sp_reads(g, [S.Many{i, Shape.sp_dec(m)}], Shape.sp_moved(Shape.sp_left(y), Shape.sp_reads(1n+g, i, [y], B)), B), Shape.sp_zero(m, y)) : List<&2, S.St>}
      +B2 = {Nat.add(B, Shape.sp_ncaps(i)) : Nat}
      +R2 = {Shape.sp_reads(1n+g, [S.Many{i, m}], rest, B) : List<&2, S.St>}
      %Equal.sym(List<&2, S.St>, Shape.sp_reads(1n+g, t, List.append(&2, S.St, A, R2), B2), List.append(&2, S.St, Shape.sp_reads(1n+g, t, A, B2), Shape.sp_reads(1n+g, t, R2, B2)), LH.shh.reads_app(1n+g, t, A, R2, B2)) : {Shape.sp_reads(1n+g, S.Many{i, m} <> t, y <> rest, B) == _ : List<&2, S.St>}
      Equal.cong(List<&2, S.St>, List<&2, S.St>, z => List.append(&2, S.St, Shape.sp_reads(1n+g, t, A, B2), z), Shape.sp_reads(1n+g, S.Many{i, m} <> t, rest, B), Shape.sp_reads(1n+g, t, R2, B2), shk.seq(g, i, m, t, rest, B))

# The fallback
# ------------

# the fallback's frames compute what they stand for
def shk.frames(+f: Nat, K: S.Fr, +xs: List<&2, S.St>) -> {S.frames(f, K, xs) == shk.kd(f, K, xs) : List<&2, S.St>}:
  match K:
    case S.FEnd{}:
      {==}
    case S.FSeq{+t, +b, +k}:
      %Equal.sym(List<&2, S.St>, S.go(f, t, xs, S.val(b)), Shape.sp_reads(f, t, xs, S.val(b)), LAll.shall.all(f, t, xs, S.val(b))) : {S.frames(f, k, _) == shk.kd(f, S.FSeq{t, b, k}, xs) : List<&2, S.St>}
      shk.frames(f, k, Shape.sp_reads(f, t, xs, S.val(b)))
    case S.FCap{+n, +at, +from, +k}:
      %Equal.sym(List<&2, S.St>, S.close(xs, n, at, from), Shape.sp_cap(xs, n, at, from), LL.shl.close(xs, n, at, from)) : {S.frames(f, k, _) == shk.kd(f, S.FCap{n, at, from, k}, xs) : List<&2, S.St>}
      shk.frames(f, k, Shape.sp_cap(xs, n, at, from))
    case S.FRound{+q, +b, +l, +k}:
      %Equal.sym(List<&2, S.St>, S.grew(l, xs), Shape.sp_moved(l, xs), LL.shl.grew(l, xs)) : {S.frames(f, k, S.go(f, S.many.next(q), _, S.val(b))) == shk.kd(f, S.FRound{q, b, l, k}, xs) : List<&2, S.St>}
      %Equal.sym(List<&2, S.St>, S.go(f, S.many.next(q), Shape.sp_moved(l, xs), S.val(b)), Shape.sp_reads(f, S.many.next(q), Shape.sp_moved(l, xs), S.val(b)), LAll.shall.all(f, S.many.next(q), Shape.sp_moved(l, xs), S.val(b))) : {S.frames(f, k, _) == shk.kd(f, S.FRound{q, b, l, k}, xs) : List<&2, S.St>}
      shk.frames(f, k, Shape.sp_reads(f, S.many.next(q), Shape.sp_moved(l, xs), S.val(b)))

# what the frames stand for does not depend on a fuel past every count
def shk.kd_fi(+F1: Nat, +F2: Nat, K: S.Fr, +X: List<&2, S.St>, +h1: {LU.shu.fits(F1, X) == True{} : Bool}, +h2: {LU.shu.fits(F2, X) == True{} : Bool}) -> {shk.kd(F1, K, X) == shk.kd(F2, K, X) : List<&2, S.St>}:
  match K:
    case S.FEnd{}:
      {==}
    case S.FSeq{+t, +b, +k}:
      %Equal.sym(List<&2, S.St>, Shape.sp_reads(F1, t, X, S.val(b)), Shape.sp_reads(F2, t, X, S.val(b)), LU.shu.fi(F1, F2, t, X, S.val(b), h1, h2)) : {shk.kd(F1, k, _) == shk.kd(F2, k, Shape.sp_reads(F2, t, X, S.val(b))) : List<&2, S.St>}
      shk.kd_fi(F1, F2, k, Shape.sp_reads(F2, t, X, S.val(b)), LU.shu.pf(F2, t, X, S.val(b), F1, h1), LU.shu.pf(F2, t, X, S.val(b), F2, h2))
    case S.FCap{+n, +at, +from, +k}:
      shk.kd_fi(F1, F2, k, Shape.sp_cap(X, n, at, from), LU.shu.cap_t(F1, X, n, at, from, h1), LU.shu.cap_t(F2, X, n, at, from, h2))
    case S.FRound{+q, +b, +l, +k}:
      +M = {Shape.sp_moved(l, X) : List<&2, S.St>}
      +m1 = {LU.shu.moved(F1, l, X, h1) : {LU.shu.fits(F1, M) == True{} : Bool}}
      +m2 = {LU.shu.moved(F2, l, X, h2) : {LU.shu.fits(F2, M) == True{} : Bool}}
      %Equal.sym(List<&2, S.St>, Shape.sp_reads(F1, S.many.next(q), M, S.val(b)), Shape.sp_reads(F2, S.many.next(q), M, S.val(b)), LU.shu.fi(F1, F2, S.many.next(q), M, S.val(b), m1, m2)) : {shk.kd(F1, k, _) == shk.kd(F2, k, Shape.sp_reads(F2, S.many.next(q), M, S.val(b))) : List<&2, S.St>}
      shk.kd_fi(F1, F2, k, Shape.sp_reads(F2, S.many.next(q), M, S.val(b)), LU.shu.pf(F2, S.many.next(q), M, S.val(b), F1, m1), LU.shu.pf(F2, S.many.next(q), M, S.val(b), F2, m2))

# with no budget left, the fallback answers the spec's first reading
def shk.out(+F: Nat, +s: S.St, +ps: List<&2, S.Piece>, +b: S.Base, +K: S.Fr, +e: Bool, +h: {Nat.is_lt(Shape.sp_left(s), F) == True{} : Bool}) -> {S.out(S.Want{s}, ps, b, K, e) == shk.G(F, K, e, ps, S.val(b), [s]) : Maybe<&2, S.St>}:
  +f = {1n+S.remain(s) : Nat}
  +B = {S.val(b) : Nat}
  +hf = {LU.shu.one(f, s, Equal.trans(Bool, Nat.is_lt(Shape.sp_left(s), f), Nat.is_lt(S.remain(s), f), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, f), Shape.sp_left(s), S.remain(s), Equal.sym(Nat, S.remain(s), Shape.sp_left(s), LL.shl.remain(s))), LS.shs.lt_self(S.remain(s)))) : {LU.shu.fits(f, [s]) == True{} : Bool}}
  +hF = {LU.shu.one(F, s, h) : {LU.shu.fits(F, [s]) == True{} : Bool}}
  %Equal.sym(Maybe<&2, S.St>, S.first_end(e, S.frames(f, K, S.go(f, ps, [s], B))), Shape.sp_head(Shape.sp_keep(e, S.frames(f, K, S.go(f, ps, [s], B)))), LF.shfe.first_end(e, S.frames(f, K, S.go(f, ps, [s], B)))) : {_ == shk.G(F, K, e, ps, B, [s]) : Maybe<&2, S.St>}
  %Equal.sym(List<&2, S.St>, S.go(f, ps, [s], B), Shape.sp_reads(f, ps, [s], B), LAll.shall.all(f, ps, [s], B)) : {Shape.sp_head(Shape.sp_keep(e, S.frames(f, K, _))) == shk.G(F, K, e, ps, B, [s]) : Maybe<&2, S.St>}
  %Equal.sym(List<&2, S.St>, S.frames(f, K, Shape.sp_reads(f, ps, [s], B)), shk.kd(f, K, Shape.sp_reads(f, ps, [s], B)), shk.frames(f, K, Shape.sp_reads(f, ps, [s], B))) : {Shape.sp_head(Shape.sp_keep(e, _)) == shk.G(F, K, e, ps, B, [s]) : Maybe<&2, S.St>}
  %Equal.sym(List<&2, S.St>, Shape.sp_reads(f, ps, [s], B), Shape.sp_reads(F, ps, [s], B), LU.shu.fi(f, F, ps, [s], B, hf, hF)) : {Shape.sp_head(Shape.sp_keep(e, shk.kd(f, K, _))) == shk.G(F, K, e, ps, B, [s]) : Maybe<&2, S.St>}
  %Equal.sym(List<&2, S.St>, shk.kd(f, K, Shape.sp_reads(F, ps, [s], B)), shk.kd(F, K, Shape.sp_reads(F, ps, [s], B)), shk.kd_fi(f, F, K, Shape.sp_reads(F, ps, [s], B), LU.shu.pf(F, ps, [s], B, f, hf), LU.shu.pf(F, ps, [s], B, F, hF))) : {Shape.sp_head(Shape.sp_keep(e, _)) == shk.G(F, K, e, ps, B, [s]) : Maybe<&2, S.St>}
  {==}

# Combinators
# -----------

def shk.fits_m(+F: Nat, m: Maybe<&2, S.St>, -P: List<&2, S.St>, hm: {S.m2l(m) == P : List<&2, S.St>}, hp: {LU.shu.fits(F, P) == True{} : Bool}) -> {LU.shu.fits(F, shk.wl(S.want(m))) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+s}:
      %Equal.sym(List<&2, S.St>, [s], P, hm) : {LU.shu.fits(F, _) == True{} : Bool}
      hp

def shk.fits_prefer(+F: Nat, x: Maybe<&2, S.St>, +m: Maybe<&2, S.St>, hm: {LU.shu.fits(F, shk.wl(S.want(m))) == True{} : Bool}) -> {LU.shu.fits(F, shk.wl(S.prefer(x, m))) == True{} : Bool}:
  match x:
    case None{}:
      hm
    case Some{r}:
      {==}

def shk.fits_zero(+F: Nat, min: Nat, +s: S.St, h: {LU.shu.fits(F, [s]) == True{} : Bool}) -> {LU.shu.fits(F, shk.wl(S.want(S.zero(min, s)))) == True{} : Bool}:
  match min:
    case 0n:
      h
    case 1n+k:
      {==}

# an answer from the place m, as the readings of t from P
def shk.via(-M: Maybe<&2, S.St>, +F: Nat, +m: Maybe<&2, S.St>, +t: List<&2, S.Piece>, +b: S.Base, +K: S.Fr, +e: Bool, +P: List<&2, S.St>, ih: {M == shk.ans(F, S.want(m), t, b, K, e) : Maybe<&2, S.St>}, hm: {S.m2l(m) == P : List<&2, S.St>}) -> {M == shk.G(F, K, e, t, S.val(b), P) : Maybe<&2, S.St>}:
  +A = {shk.ans(F, S.want(m), t, b, K, e) : Maybe<&2, S.St>}
  Equal.trans(Maybe<&2, S.St>, M, A, shk.G(F, K, e, t, S.val(b), P), ih, Equal.trans(Maybe<&2, S.St>, A, shk.G(F, K, e, t, S.val(b), S.m2l(m)), shk.G(F, K, e, t, S.val(b), P), shk.ans_want(F, m, t, b, K, e), Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, z => shk.G(F, K, e, t, S.val(b), z), S.m2l(m), P, hm)))

# the spec's answer for a piece then t from one place, its own readings P
def shk.fin(-M: Maybe<&2, S.St>, +g: Nat, +K: S.Fr, +e: Bool, +t: List<&2, S.Piece>, +B2: Nat, +P: List<&2, S.St>, +ps: List<&2, S.Piece>, +B: Nat, h: {M == shk.G(1n+g, K, e, t, B2, P) : Maybe<&2, S.St>}) -> {M == Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, K, List.append(&2, S.St, Shape.sp_reads(1n+g, t, P, B2), Shape.sp_reads(1n+g, ps, Nil{}, B))))) : Maybe<&2, S.St>}:
  Equal.trans(Maybe<&2, S.St>, M, shk.G(1n+g, K, e, t, B2, P), Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, K, List.append(&2, S.St, Shape.sp_reads(1n+g, t, P, B2), Shape.sp_reads(1n+g, ps, Nil{}, B))))), h, Equal.sym(Maybe<&2, S.St>, Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, K, List.append(&2, S.St, Shape.sp_reads(1n+g, t, P, B2), Shape.sp_reads(1n+g, ps, Nil{}, B))))), shk.G(1n+g, K, e, t, B2, P), shk.G_tail(1n+g, K, e, t, B2, P, ps, B)))

# two answers in turn: the first, else the second
def shk.or2(-M: Maybe<&2, S.St>, +F: Nat, +K: S.Fr, +e: Bool, +t: List<&2, S.Piece>, +B: Nat, -X: Maybe<&2, S.St>, +P1: List<&2, S.St>, +P2: List<&2, S.St>, h: {M == shk.or(X, shk.G(F, K, e, t, B, P2)) : Maybe<&2, S.St>}, hx: {X == shk.G(F, K, e, t, B, P1) : Maybe<&2, S.St>}) -> {M == shk.G(F, K, e, t, B, List.append(&2, S.St, P1, P2)) : Maybe<&2, S.St>}:
  %Equal.sym(Maybe<&2, S.St>, shk.G(F, K, e, t, B, List.append(&2, S.St, P1, P2)), shk.or(shk.G(F, K, e, t, B, P1), shk.G(F, K, e, t, B, P2)), shk.G_app(F, K, e, t, B, P1, P2)) : {M == _ : Maybe<&2, S.St>}
  %Equal.sym(Maybe<&2, S.St>, shk.G(F, K, e, t, B, P1), X, Equal.sym(Maybe<&2, S.St>, X, shk.G(F, K, e, t, B, P1), hx)) : {M == shk.or(_, shk.G(F, K, e, t, B, P2)) : Maybe<&2, S.St>}
  h

def shk.ncaps(+B: Nat, +i: List<&2, S.Piece>) -> {Nat.add(B, S.ncaps(i)) == Nat.add(B, Shape.sp_ncaps(i)) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(B, z), S.ncaps(i), Shape.sp_ncaps(i), LL.shl.ncaps(i))

def shk.G_base(+F: Nat, +K: S.Fr, +e: Bool, +t: List<&2, S.Piece>, -B1: Nat, -B2: Nat, +P: List<&2, S.St>, h: {B1 == B2 : Nat}) -> {shk.G(F, K, e, t, B1, P) == shk.G(F, K, e, t, B2, P) : Maybe<&2, S.St>}:
  Equal.cong(Nat, Maybe<&2, S.St>, z => shk.G(F, K, e, t, z, P), B1, B2, h)

# Run
# ---

# the spec's run readings past one more char (the longest first), none
# at the text end
def shk.run_more(+c: S.Cls, min: Nat, +max: Maybe<&2, Nat>, s: S.St) -> List<&2, S.St>:
  match s:
    case S.St{pos, left, word, rest, caps}:
      match rest:
        case SNil{}:
          Nil{}
        case SCon{+x, t}:
          Shape.sp_if(Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)), Shape.sp_run.go(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps))

def shk.run_split(c: S.Cls, min: Nat, max: Maybe<&2, Nat>, s: S.St) -> {Shape.sp_run(c, min, max, s) == List.append(&2, S.St, shk.run_more(c, min, max, s), Shape.sp_zero(min, s)) : List<&2, S.St>}:
  match s:
    case S.St{pos, left, word, rest, caps}:
      match rest:
        case SNil{}:
          {==}
        case SCon{x, t}:
          {==}

def shk.run_step.at(+g: Nat, +K: S.Fr, +e: Bool, +c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +t: List<&2, S.Piece>, +B: Nat, b: Bool, +x: S.St) -> {shk.G(1n+g, K, e, S.Run{c, min, max} <> t, B, S.m2l(S.keep(b, x))) == shk.G(1n+g, K, e, t, B, Shape.sp_if(b, Shape.sp_run(c, min, max, x))) : Maybe<&2, S.St>}:
  match b:
    case True{}:
      shk.G_tail(1n+g, K, e, t, B, Shape.sp_run(c, min, max, x), S.Run{c, min, max} <> t, B)
    case False{}:
      Equal.trans(Maybe<&2, S.St>, shk.G(1n+g, K, e, S.Run{c, min, max} <> t, B, Nil{}), None{}, shk.G(1n+g, K, e, t, B, Nil{}), shk.G_nil(1n+g, K, e, S.Run{c, min, max} <> t, B), Equal.sym(Maybe<&2, S.St>, shk.G(1n+g, K, e, t, B, Nil{}), None{}, shk.G_nil(1n+g, K, e, t, B)))

# Run: the readings past one more char, as the spec's
def shk.run_step(+g: Nat, +K: S.Fr, +e: Bool, +c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +t: List<&2, S.Piece>, +B: Nat, s: S.St) -> {shk.G(1n+g, K, e, S.Run{c, Shape.sp_dec(min), Shape.sp_less(max)} <> t, B, S.m2l(S.run.step(c, max, s))) == shk.G(1n+g, K, e, t, B, shk.run_more(c, min, max, s)) : Maybe<&2, S.St>}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      match rest:
        case SNil{}:
          +R = {S.Run{c, Shape.sp_dec(min), Shape.sp_less(max)} <> t : List<&2, S.Piece>}
          Equal.trans(Maybe<&2, S.St>, shk.G(1n+g, K, e, R, B, Nil{}), None{}, shk.G(1n+g, K, e, t, B, Nil{}), shk.G_nil(1n+g, K, e, R, B), Equal.sym(Maybe<&2, S.St>, shk.G(1n+g, K, e, t, B, Nil{}), None{}, shk.G_nil(1n+g, K, e, t, B)))
        case SCon{+x, +u}:
          +R = {S.Run{c, Shape.sp_dec(min), Shape.sp_less(max)} <> t : List<&2, S.Piece>}
          %Equal.sym(Bool, S.run.room(max), Shape.sp_room(max), LL.shl.room(max)) : {shk.G(1n+g, K, e, R, B, S.m2l(S.keep(Bool.and(_, S.is_in(c, x)), S.St{1n+pos, S.pred(left), S.is_word(x), u, caps}))) == shk.G(1n+g, K, e, t, B, shk.run_more(c, min, max, S.St{pos, left, word, SCon{x, u}, caps})) : Maybe<&2, S.St>}
          %Equal.sym(Bool, S.is_in(c, x), Shape.sp_cls(c, x), LL.shl.cls(c, x)) : {shk.G(1n+g, K, e, R, B, S.m2l(S.keep(Bool.and(Shape.sp_room(max), _), S.St{1n+pos, S.pred(left), S.is_word(x), u, caps}))) == shk.G(1n+g, K, e, t, B, shk.run_more(c, min, max, S.St{pos, left, word, SCon{x, u}, caps})) : Maybe<&2, S.St>}
          %Equal.sym(Nat, S.pred(left), Shape.sp_dec(left), LL.shl.pred(left)) : {shk.G(1n+g, K, e, R, B, S.m2l(S.keep(Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)), S.St{1n+pos, _, S.is_word(x), u, caps}))) == shk.G(1n+g, K, e, t, B, shk.run_more(c, min, max, S.St{pos, left, word, SCon{x, u}, caps})) : Maybe<&2, S.St>}
          %Equal.sym(Bool, S.is_word(x), Shape.sp_word(x), LL.shl.word(x)) : {shk.G(1n+g, K, e, R, B, S.m2l(S.keep(Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)), S.St{1n+pos, Shape.sp_dec(left), _, u, caps}))) == shk.G(1n+g, K, e, t, B, shk.run_more(c, min, max, S.St{pos, left, word, SCon{x, u}, caps})) : Maybe<&2, S.St>}
          shk.run_step.at(g, K, e, c, Shape.sp_dec(min), Shape.sp_less(max), t, B, Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)), S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), u, caps})

def shk.fits_keep(+F: Nat, b: Bool, +x: S.St, h: {Nat.is_lt(Shape.sp_left(x), F) == True{} : Bool}) -> {LU.shu.fits(F, shk.wl(S.want(S.keep(b, x)))) == True{} : Bool}:
  match b:
    case True{}:
      LU.shu.one(F, x, h)
    case False{}:
      {==}

def shk.fits_step(+F: Nat, c: S.Cls, max: Maybe<&2, Nat>, s: S.St, h: {Nat.is_lt(Shape.sp_left(s), F) == True{} : Bool}) -> {LU.shu.fits(F, shk.wl(S.want(S.run.step(c, max, s)))) == True{} : Bool}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      match rest:
        case SNil{}:
          {==}
        case SCon{+x, +u}:
          +hl = {Equal.trans(Bool, Nat.is_lt(S.pred(left), F), Nat.is_lt(Shape.sp_dec(left), F), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, F), S.pred(left), Shape.sp_dec(left), LL.shl.pred(left)), LU.shu.lt_dec(left, F, h)) : {Nat.is_lt(S.pred(left), F) == True{} : Bool}}
          shk.fits_keep(F, Bool.and(S.run.room(max), S.is_in(c, x)), S.St{1n+pos, S.pred(left), S.is_word(x), u, caps}, hl)

# Cases
# -----

# a piece that reads no inner pieces: the place m its reading, P the spec's
def shk.leaf(-M: Maybe<&2, S.St>, +g: Nat, +m: Maybe<&2, S.St>, +t: List<&2, S.Piece>, +b: S.Base, +K: S.Fr, +e: Bool, +P: List<&2, S.St>, +ps: List<&2, S.Piece>, ih: {M == shk.ans(1n+g, S.want(m), t, b, K, e) : Maybe<&2, S.St>}, hm: {S.m2l(m) == P : List<&2, S.St>}) -> {M == Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, K, List.append(&2, S.St, Shape.sp_reads(1n+g, t, P, S.val(b)), Shape.sp_reads(1n+g, ps, Nil{}, S.val(b)))))) : Maybe<&2, S.St>}:
  shk.fin(M, g, K, e, t, S.val(b), P, ps, S.val(b), shk.via(M, 1n+g, m, t, b, K, e, P, ih, hm))

def shk.set1(s: S.St, +n: Nat, +at: Nat, +from: String) -> {[S.set(s, n, at, from)] == Shape.sp_cap([s], n, at, from) : List<&2, S.St>}:
  match s:
    case S.St{pos, left, word, rest, caps}:
      {==}

def shk.fits_set(+F: Nat, s: S.St, +n: Nat, +at: Nat, +from: String, h: {LU.shu.fits(F, [s]) == True{} : Bool}) -> {LU.shu.fits(F, [S.set(s, n, at, from)]) == True{} : Bool}:
  match s:
    case S.St{pos, left, word, rest, caps}:
      h

# The matcher
# -----------

# the matcher answers the spec's first reading, for every fuel past the
# count of chars after its place
def shk.seek(T: Nat, w: S.W, +F: Nat, +ps: List<&2, S.Piece>, +b: S.Base, +K: S.Fr, +e: Bool, +h: {LU.shu.fits(F, shk.wl(w)) == True{} : Bool}) -> {S.seek(T, w, ps, b, K, e) == shk.ans(F, w, ps, b, K, e) : Maybe<&2, S.St>}:
  match T:
    case 0n:
      match w:
        case S.Want{+s}:
          shk.out(F, s, ps, b, K, e, LU.shu.head(F, s, Nil{}, h))
        case S.Have{r}:
          {==}
        case S.Nothing{}:
          {==}
    case 1n++U:
      match w:
        case S.Have{r}:
          {==}
        case S.Nothing{}:
          {==}
        case S.Want{+s}:
          match F:
            case 0n:
              LU.shu.fits0({S.seek(1n+U, S.Want{s}, ps, b, K, e) == shk.ans(0n, S.Want{s}, ps, b, K, e) : Maybe<&2, S.St>}, s, Nil{}, h)
            case 1n++g:
              match ps:
                case Nil{}:
                  match K:
                    case S.FEnd{}:
                      shk.done(e, s)
                    case S.FSeq{+t, +c, +k}:
                      shk.seek(U, S.Want{s}, 1n+g, t, c, k, e, h)
                    case S.FCap{+n, +at, +from, +k}:
                      +M = {S.seek(U, S.Want{S.set(s, n, at, from)}, Nil{}, b, k, e) : Maybe<&2, S.St>}
                      +ih = {shk.seek(U, S.Want{S.set(s, n, at, from)}, 1n+g, Nil{}, b, k, e, shk.fits_set(1n+g, s, n, at, from, h)) : {M == shk.ans(1n+g, S.Want{S.set(s, n, at, from)}, Nil{}, b, k, e) : Maybe<&2, S.St>}}
                      Equal.trans(Maybe<&2, S.St>, M, Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, k, [S.set(s, n, at, from)]))), Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, k, Shape.sp_cap([s], n, at, from)))), ih, Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, z => Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, k, z))), [S.set(s, n, at, from)], Shape.sp_cap([s], n, at, from), shk.set1(s, n, at, from)))
                    case S.FRound{+q, +c, +l, +k}:
                      +M = {S.seek(U, S.want(S.moved(l, s)), S.many.next(q), c, k, e) : Maybe<&2, S.St>}
                      +hm = {shk.moved1(l, s) : {S.m2l(S.moved(l, s)) == Shape.sp_moved(l, [s]) : List<&2, S.St>}}
                      shk.via(M, 1n+g, S.moved(l, s), S.many.next(q), c, k, e, Shape.sp_moved(l, [s]), shk.seek(U, S.want(S.moved(l, s)), 1n+g, S.many.next(q), c, k, e, shk.fits_m(1n+g, S.moved(l, s), Shape.sp_moved(l, [s]), hm, LU.shu.moved(1n+g, l, [s], h))), hm)
                case q <> +t:
                  match q:
                    case S.Lit{+u}:
                      +hs = {LU.shu.head(1n+g, s, Nil{}, h) : {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}}
                      +m = {S.lit(u, False{}, s) : Maybe<&2, S.St>}
                      +P = {Shape.sp_eat(u, False{}, s) : List<&2, S.St>}
                      +hm = {LL.shl.lit(u, False{}, s) : {S.m2l(m) == P : List<&2, S.St>}}
                      shk.leaf(S.seek(U, S.want(m), t, b, K, e), g, m, t, b, K, e, P, S.Lit{u} <> t, shk.seek(U, S.want(m), 1n+g, t, b, K, e, shk.fits_m(1n+g, m, P, hm, LU.shu.eat(u, False{}, s, 1n+g, hs))), hm)
                    case S.Fold{+u}:
                      +hs = {LU.shu.head(1n+g, s, Nil{}, h) : {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}}
                      +m = {S.lit(u, True{}, s) : Maybe<&2, S.St>}
                      +P = {Shape.sp_eat(u, True{}, s) : List<&2, S.St>}
                      +hm = {LL.shl.lit(u, True{}, s) : {S.m2l(m) == P : List<&2, S.St>}}
                      shk.leaf(S.seek(U, S.want(m), t, b, K, e), g, m, t, b, K, e, P, S.Fold{u} <> t, shk.seek(U, S.want(m), 1n+g, t, b, K, e, shk.fits_m(1n+g, m, P, hm, LU.shu.eat(u, True{}, s, 1n+g, hs))), hm)
                    case S.Same{+k}:
                      +hs = {LU.shu.head(1n+g, s, Nil{}, h) : {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}}
                      +m = {S.same(k, s) : Maybe<&2, S.St>}
                      +P = {Shape.sp_same(k, s) : List<&2, S.St>}
                      +hm = {LL.shl.same_k(k, s) : {S.m2l(m) == P : List<&2, S.St>}}
                      shk.leaf(S.seek(U, S.want(m), t, b, K, e), g, m, t, b, K, e, P, S.Same{k} <> t, shk.seek(U, S.want(m), 1n+g, t, b, K, e, shk.fits_m(1n+g, m, P, hm, LU.shu.same(k, s, 1n+g, hs))), hm)
                    case S.Bound{}:
                      +hs = {LU.shu.head(1n+g, s, Nil{}, h) : {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}}
                      +m = {S.bound(s) : Maybe<&2, S.St>}
                      +P = {Shape.sp_bound(s) : List<&2, S.St>}
                      +hm = {LL.shl.bound(s) : {S.m2l(m) == P : List<&2, S.St>}}
                      shk.leaf(S.seek(U, S.want(m), t, b, K, e), g, m, t, b, K, e, P, S.Bound{} <> t, shk.seek(U, S.want(m), 1n+g, t, b, K, e, shk.fits_m(1n+g, m, P, hm, LU.shu.bound(s, 1n+g, hs))), hm)
                    case S.Begin{}:
                      +hs = {LU.shu.head(1n+g, s, Nil{}, h) : {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}}
                      +m = {S.begin(s) : Maybe<&2, S.St>}
                      +P = {Shape.sp_begin(s) : List<&2, S.St>}
                      +hm = {LL.shl.begin(s) : {S.m2l(m) == P : List<&2, S.St>}}
                      shk.leaf(S.seek(U, S.want(m), t, b, K, e), g, m, t, b, K, e, P, S.Begin{} <> t, shk.seek(U, S.want(m), 1n+g, t, b, K, e, shk.fits_m(1n+g, m, P, hm, LU.shu.begin(s, 1n+g, hs))), hm)
                    case S.End{}:
                      +hs = {LU.shu.head(1n+g, s, Nil{}, h) : {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}}
                      +m = {S.end(s) : Maybe<&2, S.St>}
                      +P = {Shape.sp_end(s) : List<&2, S.St>}
                      +hm = {LL.shl.end(s) : {S.m2l(m) == P : List<&2, S.St>}}
                      shk.leaf(S.seek(U, S.want(m), t, b, K, e), g, m, t, b, K, e, P, S.End{} <> t, shk.seek(U, S.want(m), 1n+g, t, b, K, e, shk.fits_m(1n+g, m, P, hm, LU.shu.end(s, 1n+g, hs))), hm)
                    case S.Run{+c, +min, +max}:
                      +hs = {LU.shu.head(1n+g, s, Nil{}, h) : {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}}
                      +B = {S.val(b) : Nat}
                      +st = {S.run.step(c, max, s) : Maybe<&2, S.St>}
                      +nx = {S.run.next(min, max, c, t, S.Run{c, min, max} <> t) : List<&2, S.Piece>}
                      +R2 = {S.Run{c, Shape.sp_dec(min), Shape.sp_less(max)} <> t : List<&2, S.Piece>}
                      +X = {S.seek(U, S.want(st), nx, b, K, e) : Maybe<&2, S.St>}
                      +M = {S.seek(U, S.prefer(X, S.zero(min, s)), t, b, K, e) : Maybe<&2, S.St>}
                      +MR = {shk.run_more(c, min, max, s) : List<&2, S.St>}
                      +ihX = {shk.seek(U, S.want(st), 1n+g, nx, b, K, e, shk.fits_step(1n+g, c, max, s, hs)) : {X == shk.ans(1n+g, S.want(st), nx, b, K, e) : Maybe<&2, S.St>}}
                      +hX = {Equal.trans(Maybe<&2, S.St>, X, shk.ans(1n+g, S.want(st), nx, b, K, e), shk.G(1n+g, K, e, t, B, MR), ihX, Equal.trans(Maybe<&2, S.St>, shk.ans(1n+g, S.want(st), nx, b, K, e), shk.G(1n+g, K, e, nx, B, S.m2l(st)), shk.G(1n+g, K, e, t, B, MR), shk.ans_want(1n+g, st, nx, b, K, e), Equal.trans(Maybe<&2, S.St>, shk.G(1n+g, K, e, nx, B, S.m2l(st)), shk.G(1n+g, K, e, R2, B, S.m2l(st)), shk.G(1n+g, K, e, t, B, MR), Equal.cong(List<&2, S.Piece>, Maybe<&2, S.St>, z => shk.G(1n+g, K, e, z, B, S.m2l(st)), nx, R2, shk.run_next(c, min, max, t)), shk.run_step(g, K, e, c, min, max, t, B, s)))) : {X == shk.G(1n+g, K, e, t, B, MR) : Maybe<&2, S.St>}}
                      +ihO = {shk.seek(U, S.prefer(X, S.zero(min, s)), 1n+g, t, b, K, e, shk.fits_prefer(1n+g, X, S.zero(min, s), shk.fits_zero(1n+g, min, s, h))) : {M == shk.ans(1n+g, S.prefer(X, S.zero(min, s)), t, b, K, e) : Maybe<&2, S.St>}}
                      +hO = {Equal.trans(Maybe<&2, S.St>, M, shk.ans(1n+g, S.prefer(X, S.zero(min, s)), t, b, K, e), shk.or(X, shk.G(1n+g, K, e, t, B, Shape.sp_zero(min, s))), ihO, Equal.trans(Maybe<&2, S.St>, shk.ans(1n+g, S.prefer(X, S.zero(min, s)), t, b, K, e), shk.or(X, shk.G(1n+g, K, e, t, B, S.m2l(S.zero(min, s)))), shk.or(X, shk.G(1n+g, K, e, t, B, Shape.sp_zero(min, s))), shk.ans_prefer(1n+g, X, S.zero(min, s), t, b, K, e), Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, z => shk.or(X, shk.G(1n+g, K, e, t, B, z)), S.m2l(S.zero(min, s)), Shape.sp_zero(min, s), LL.shl.zero(min, s)))) : {M == shk.or(X, shk.G(1n+g, K, e, t, B, Shape.sp_zero(min, s))) : Maybe<&2, S.St>}}
                      +h2 = {shk.or2(M, 1n+g, K, e, t, B, X, MR, Shape.sp_zero(min, s), hO, hX) : {M == shk.G(1n+g, K, e, t, B, List.append(&2, S.St, MR, Shape.sp_zero(min, s))) : Maybe<&2, S.St>}}
                      +h3 = {Equal.trans(Maybe<&2, S.St>, M, shk.G(1n+g, K, e, t, B, List.append(&2, S.St, MR, Shape.sp_zero(min, s))), shk.G(1n+g, K, e, t, B, Shape.sp_run(c, min, max, s)), h2, Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, z => shk.G(1n+g, K, e, t, B, z), List.append(&2, S.St, MR, Shape.sp_zero(min, s)), Shape.sp_run(c, min, max, s), Equal.sym(List<&2, S.St>, Shape.sp_run(c, min, max, s), List.append(&2, S.St, MR, Shape.sp_zero(min, s)), shk.run_split(c, min, max, s)))) : {M == shk.G(1n+g, K, e, t, B, Shape.sp_run(c, min, max, s)) : Maybe<&2, S.St>}}
                      shk.fin(M, g, K, e, t, B, Shape.sp_run(c, min, max, s), S.Run{c, min, max} <> t, B, h3)
                    case S.Cap{+i}:
                      +B = {S.val(b) : Nat}
                      +V = {S.BAfter{S.BAt{1n+B}, i} : S.Base}
                      +P0 = {S.push(t, V, K) : S.Fr}
                      +R = {Shape.sp_reads(1n+g, i, [s], 1n+B) : List<&2, S.St>}
                      +CP = {Shape.sp_cap(R, B, S.place(s), S.after(s)) : List<&2, S.St>}
                      +CS = {Shape.sp_cap(R, B, Shape.sp_pos(s), Shape.sp_text(s)) : List<&2, S.St>}
                      +B2 = {1n+Nat.add(B, Shape.sp_ncaps(i)) : Nat}
                      +M = {S.seek(U, S.Want{s}, i, S.BAt{1n+B}, S.FCap{B, S.place(s), S.after(s), P0}, e) : Maybe<&2, S.St>}
                      +ih = {shk.seek(U, S.Want{s}, 1n+g, i, S.BAt{1n+B}, S.FCap{B, S.place(s), S.after(s), P0}, e, h) : {M == Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, P0, CP))) : Maybe<&2, S.St>}}
                      +h1 = {Equal.trans(Maybe<&2, S.St>, M, Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, P0, CP))), shk.G(1n+g, K, e, t, S.val(V), CP), ih, Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, z => Shape.sp_head(Shape.sp_keep(e, z)), shk.kd(1n+g, P0, CP), shk.kd(1n+g, K, Shape.sp_reads(1n+g, t, CP, S.val(V))), shk.push(g, t, V, K, CP))) : {M == shk.G(1n+g, K, e, t, S.val(V), CP) : Maybe<&2, S.St>}}
                      +h2 = {shk.G_base(1n+g, K, e, t, S.val(V), B2, CP, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(B, S.ncaps(i)), Nat.add(B, Shape.sp_ncaps(i)), shk.ncaps(B, i))) : {shk.G(1n+g, K, e, t, S.val(V), CP) == shk.G(1n+g, K, e, t, B2, CP) : Maybe<&2, S.St>}}
                      +h3 = {Equal.trans(List<&2, S.St>, CP, Shape.sp_cap(R, B, Shape.sp_pos(s), S.after(s)), CS, Equal.cong(Nat, List<&2, S.St>, z => Shape.sp_cap(R, B, z, S.after(s)), S.place(s), Shape.sp_pos(s), LL.shl.place(s)), Equal.cong(String, List<&2, S.St>, z => Shape.sp_cap(R, B, Shape.sp_pos(s), z), S.after(s), Shape.sp_text(s), LL.shl.after(s))) : {CP == CS : List<&2, S.St>}}
                      shk.fin(M, g, K, e, t, B2, CS, S.Cap{i} <> t, B, Equal.trans(Maybe<&2, S.St>, M, shk.G(1n+g, K, e, t, B2, CP), shk.G(1n+g, K, e, t, B2, CS), Equal.trans(Maybe<&2, S.St>, M, shk.G(1n+g, K, e, t, S.val(V), CP), shk.G(1n+g, K, e, t, B2, CP), h1, h2), Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, z => shk.G(1n+g, K, e, t, B2, z), CP, CS, h3)))
                    case S.Opt{+i}:
                      +B = {S.val(b) : Nat}
                      +c = {S.BAfter{b, i} : S.Base}
                      +R = {Shape.sp_reads(1n+g, i, [s], B) : List<&2, S.St>}
                      +X = {S.seek(U, S.Want{s}, i, b, S.push(t, c, K), e) : Maybe<&2, S.St>}
                      +M = {S.seek(U, S.prefer(X, Some{s}), t, c, K, e) : Maybe<&2, S.St>}
                      +hX = {Equal.trans(Maybe<&2, S.St>, X, shk.G(1n+g, S.push(t, c, K), e, i, B, [s]), shk.G(1n+g, K, e, t, S.val(c), R), shk.seek(U, S.Want{s}, 1n+g, i, b, S.push(t, c, K), e, h), shk.G_push(g, t, c, K, e, i, B, [s])) : {X == shk.G(1n+g, K, e, t, S.val(c), R) : Maybe<&2, S.St>}}
                      +hO = {Equal.trans(Maybe<&2, S.St>, M, shk.ans(1n+g, S.prefer(X, Some{s}), t, c, K, e), shk.or(X, shk.G(1n+g, K, e, t, S.val(c), [s])), shk.seek(U, S.prefer(X, Some{s}), 1n+g, t, c, K, e, shk.fits_prefer(1n+g, X, Some{s}, h)), shk.ans_prefer(1n+g, X, Some{s}, t, c, K, e)) : {M == shk.or(X, shk.G(1n+g, K, e, t, S.val(c), [s])) : Maybe<&2, S.St>}}
                      +h2 = {shk.or2(M, 1n+g, K, e, t, S.val(c), X, R, [s], hO, hX) : {M == shk.G(1n+g, K, e, t, S.val(c), List.append(&2, S.St, R, [s])) : Maybe<&2, S.St>}}
                      shk.fin(M, g, K, e, t, Nat.add(B, Shape.sp_ncaps(i)), List.append(&2, S.St, R, [s]), S.Opt{i} <> t, B, Equal.trans(Maybe<&2, S.St>, M, shk.G(1n+g, K, e, t, S.val(c), List.append(&2, S.St, R, [s])), shk.G(1n+g, K, e, t, Nat.add(B, Shape.sp_ncaps(i)), List.append(&2, S.St, R, [s])), h2, shk.G_base(1n+g, K, e, t, S.val(c), Nat.add(B, Shape.sp_ncaps(i)), List.append(&2, S.St, R, [s]), shk.ncaps(B, i))))
                    case S.Alt{+a, +c}:
                      +B = {S.val(b) : Nat}
                      +d = {S.BAfter{b, a} : S.Base}
                      +V = {S.BAfter{d, c} : S.Base}
                      +K2 = {S.push(t, V, K) : S.Fr}
                      +Ra = {Shape.sp_reads(1n+g, a, [s], B) : List<&2, S.St>}
                      +Rc = {Shape.sp_reads(1n+g, c, [s], S.val(d)) : List<&2, S.St>}
                      +Rs = {Shape.sp_reads(1n+g, c, [s], Nat.add(B, Shape.sp_ncaps(a))) : List<&2, S.St>}
                      +BV = {Nat.add(Nat.add(B, Shape.sp_ncaps(a)), Shape.sp_ncaps(c)) : Nat}
                      +X = {S.seek(U, S.Want{s}, a, b, K2, e) : Maybe<&2, S.St>}
                      +M = {S.seek(U, S.prefer(X, Some{s}), c, d, K2, e) : Maybe<&2, S.St>}
                      +hX = {Equal.trans(Maybe<&2, S.St>, X, shk.G(1n+g, K2, e, a, B, [s]), shk.G(1n+g, K, e, t, S.val(V), Ra), shk.seek(U, S.Want{s}, 1n+g, a, b, K2, e, h), shk.G_push(g, t, V, K, e, a, B, [s])) : {X == shk.G(1n+g, K, e, t, S.val(V), Ra) : Maybe<&2, S.St>}}
                      +hO1 = {Equal.trans(Maybe<&2, S.St>, M, shk.ans(1n+g, S.prefer(X, Some{s}), c, d, K2, e), shk.or(X, shk.G(1n+g, K2, e, c, S.val(d), [s])), shk.seek(U, S.prefer(X, Some{s}), 1n+g, c, d, K2, e, shk.fits_prefer(1n+g, X, Some{s}, h)), shk.ans_prefer(1n+g, X, Some{s}, c, d, K2, e)) : {M == shk.or(X, shk.G(1n+g, K2, e, c, S.val(d), [s])) : Maybe<&2, S.St>}}
                      +hO = {Equal.trans(Maybe<&2, S.St>, M, shk.or(X, shk.G(1n+g, K2, e, c, S.val(d), [s])), shk.or(X, shk.G(1n+g, K, e, t, S.val(V), Rc)), hO1, Equal.cong(Maybe<&2, S.St>, Maybe<&2, S.St>, z => shk.or(X, z), shk.G(1n+g, K2, e, c, S.val(d), [s]), shk.G(1n+g, K, e, t, S.val(V), Rc), shk.G_push(g, t, V, K, e, c, S.val(d), [s]))) : {M == shk.or(X, shk.G(1n+g, K, e, t, S.val(V), Rc)) : Maybe<&2, S.St>}}
                      +h2 = {shk.or2(M, 1n+g, K, e, t, S.val(V), X, Ra, Rc, hO, hX) : {M == shk.G(1n+g, K, e, t, S.val(V), List.append(&2, S.St, Ra, Rc)) : Maybe<&2, S.St>}}
                      +h3 = {shk.G_base(1n+g, K, e, t, S.val(V), BV, List.append(&2, S.St, Ra, Rc), LAll.shall.ncaps2(B, a, c)) : {shk.G(1n+g, K, e, t, S.val(V), List.append(&2, S.St, Ra, Rc)) == shk.G(1n+g, K, e, t, BV, List.append(&2, S.St, Ra, Rc)) : Maybe<&2, S.St>}}
                      +h4 = {Equal.cong(Nat, Maybe<&2, S.St>, z => shk.G(1n+g, K, e, t, BV, List.append(&2, S.St, Ra, Shape.sp_reads(1n+g, c, [s], z))), S.val(d), Nat.add(B, Shape.sp_ncaps(a)), shk.ncaps(B, a)) : {shk.G(1n+g, K, e, t, BV, List.append(&2, S.St, Ra, Rc)) == shk.G(1n+g, K, e, t, BV, List.append(&2, S.St, Ra, Rs)) : Maybe<&2, S.St>}}
                      shk.fin(M, g, K, e, t, BV, List.append(&2, S.St, Ra, Rs), S.Alt{a, c} <> t, B, Equal.trans(Maybe<&2, S.St>, M, shk.G(1n+g, K, e, t, BV, List.append(&2, S.St, Ra, Rc)), shk.G(1n+g, K, e, t, BV, List.append(&2, S.St, Ra, Rs)), Equal.trans(Maybe<&2, S.St>, M, shk.G(1n+g, K, e, t, S.val(V), List.append(&2, S.St, Ra, Rc)), shk.G(1n+g, K, e, t, BV, List.append(&2, S.St, Ra, Rc)), h2, h3), h4))
                    case S.Many{+i, +min}:
                      +hs = {LU.shu.head(1n+g, s, Nil{}, h) : {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}}
                      +B = {S.val(b) : Nat}
                      +BI = {Nat.add(B, Shape.sp_ncaps(i)) : Nat}
                      +Q = {S.Many{i, min} <> t : List<&2, S.Piece>}
                      +Q2 = {S.Many{i, Shape.sp_dec(min)} <> t : List<&2, S.Piece>}
                      +MQ = {[S.Many{i, Shape.sp_dec(min)}] : List<&2, S.Piece>}
                      +R = {Shape.sp_reads(1n+g, i, [s], B) : List<&2, S.St>}
                      +Y = {Shape.sp_moved(Shape.sp_left(s), R) : List<&2, S.St>}
                      +A = {Shape.sp_reads(g, MQ, Y, B) : List<&2, S.St>}
                      +X = {S.seek(U, S.Want{s}, i, b, S.FRound{Q, b, S.remain(s), K}, e) : Maybe<&2, S.St>}
                      +M = {S.seek(U, S.prefer(X, S.zero(min, s)), t, S.BAfter{b, i}, K, e) : Maybe<&2, S.St>}
                      +L0 = {Shape.sp_reads(1n+g, S.many.next(Q), Shape.sp_moved(S.remain(s), R), B) : List<&2, S.St>}
                      +e1 = {Equal.cong(List<&2, S.Piece>, List<&2, S.St>, z => Shape.sp_reads(1n+g, z, Shape.sp_moved(S.remain(s), R), B), S.many.next(Q), Q2, shk.many_next(i, min, t)) : {L0 == Shape.sp_reads(1n+g, Q2, Shape.sp_moved(S.remain(s), R), B) : List<&2, S.St>}}
                      +e2 = {Equal.cong(Nat, List<&2, S.St>, z => Shape.sp_reads(1n+g, Q2, Shape.sp_moved(z, R), B), S.remain(s), Shape.sp_left(s), LL.shl.remain(s)) : {Shape.sp_reads(1n+g, Q2, Shape.sp_moved(S.remain(s), R), B) == Shape.sp_reads(1n+g, Q2, Y, B) : List<&2, S.St>}}
                      +e3 = {shk.seq(g, i, Shape.sp_dec(min), t, Y, B) : {Shape.sp_reads(1n+g, Q2, Y, B) == Shape.sp_reads(1n+g, t, Shape.sp_reads(1n+g, MQ, Y, B), BI) : List<&2, S.St>}}
                      +fF = {LU.shu.moved(1n+g, Shape.sp_left(s), R, LU.shu.pf(1n+g, i, [s], B, 1n+g, h)) : {LU.shu.fits(1n+g, Y) == True{} : Bool}}
                      +fg = {LU.shu.moved_lt(g, Shape.sp_left(s), R, hs) : {LU.shu.fits(g, Y) == True{} : Bool}}
                      +e4 = {Equal.cong(List<&2, S.St>, List<&2, S.St>, z => Shape.sp_reads(1n+g, t, z, BI), Shape.sp_reads(1n+g, MQ, Y, B), A, LU.shu.fi(1n+g, g, MQ, Y, B, fF, fg)) : {Shape.sp_reads(1n+g, t, Shape.sp_reads(1n+g, MQ, Y, B), BI) == Shape.sp_reads(1n+g, t, A, BI) : List<&2, S.St>}}
                      +eL = {Equal.trans(List<&2, S.St>, L0, Shape.sp_reads(1n+g, Q2, Shape.sp_moved(S.remain(s), R), B), Shape.sp_reads(1n+g, t, A, BI), e1, Equal.trans(List<&2, S.St>, Shape.sp_reads(1n+g, Q2, Shape.sp_moved(S.remain(s), R), B), Shape.sp_reads(1n+g, Q2, Y, B), Shape.sp_reads(1n+g, t, A, BI), e2, Equal.trans(List<&2, S.St>, Shape.sp_reads(1n+g, Q2, Y, B), Shape.sp_reads(1n+g, t, Shape.sp_reads(1n+g, MQ, Y, B), BI), Shape.sp_reads(1n+g, t, A, BI), e3, e4))) : {L0 == Shape.sp_reads(1n+g, t, A, BI) : List<&2, S.St>}}
                      +hX = {Equal.trans(Maybe<&2, S.St>, X, Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, K, L0))), shk.G(1n+g, K, e, t, BI, A), shk.seek(U, S.Want{s}, 1n+g, i, b, S.FRound{Q, b, S.remain(s), K}, e, h), Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, z => Shape.sp_head(Shape.sp_keep(e, shk.kd(1n+g, K, z))), L0, Shape.sp_reads(1n+g, t, A, BI), eL)) : {X == shk.G(1n+g, K, e, t, BI, A) : Maybe<&2, S.St>}}
                      +hO1 = {Equal.trans(Maybe<&2, S.St>, M, shk.ans(1n+g, S.prefer(X, S.zero(min, s)), t, S.BAfter{b, i}, K, e), shk.or(X, shk.G(1n+g, K, e, t, Nat.add(B, S.ncaps(i)), S.m2l(S.zero(min, s)))), shk.seek(U, S.prefer(X, S.zero(min, s)), 1n+g, t, S.BAfter{b, i}, K, e, shk.fits_prefer(1n+g, X, S.zero(min, s), shk.fits_zero(1n+g, min, s, h))), shk.ans_prefer(1n+g, X, S.zero(min, s), t, S.BAfter{b, i}, K, e)) : {M == shk.or(X, shk.G(1n+g, K, e, t, Nat.add(B, S.ncaps(i)), S.m2l(S.zero(min, s)))) : Maybe<&2, S.St>}}
                      +hO2 = {Equal.trans(Maybe<&2, S.St>, shk.G(1n+g, K, e, t, Nat.add(B, S.ncaps(i)), S.m2l(S.zero(min, s))), shk.G(1n+g, K, e, t, BI, S.m2l(S.zero(min, s))), shk.G(1n+g, K, e, t, BI, Shape.sp_zero(min, s)), shk.G_base(1n+g, K, e, t, Nat.add(B, S.ncaps(i)), BI, S.m2l(S.zero(min, s)), shk.ncaps(B, i)), Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, z => shk.G(1n+g, K, e, t, BI, z), S.m2l(S.zero(min, s)), Shape.sp_zero(min, s), LL.shl.zero(min, s))) : {shk.G(1n+g, K, e, t, Nat.add(B, S.ncaps(i)), S.m2l(S.zero(min, s))) == shk.G(1n+g, K, e, t, BI, Shape.sp_zero(min, s)) : Maybe<&2, S.St>}}
                      +hO = {Equal.trans(Maybe<&2, S.St>, M, shk.or(X, shk.G(1n+g, K, e, t, Nat.add(B, S.ncaps(i)), S.m2l(S.zero(min, s)))), shk.or(X, shk.G(1n+g, K, e, t, BI, Shape.sp_zero(min, s))), hO1, Equal.cong(Maybe<&2, S.St>, Maybe<&2, S.St>, z => shk.or(X, z), shk.G(1n+g, K, e, t, Nat.add(B, S.ncaps(i)), S.m2l(S.zero(min, s))), shk.G(1n+g, K, e, t, BI, Shape.sp_zero(min, s)), hO2)) : {M == shk.or(X, shk.G(1n+g, K, e, t, BI, Shape.sp_zero(min, s))) : Maybe<&2, S.St>}}
                      shk.fin(M, g, K, e, t, BI, List.append(&2, S.St, A, Shape.sp_zero(min, s)), Q, B, shk.or2(M, 1n+g, K, e, t, BI, X, A, Shape.sp_zero(min, s), hO, hX))
                    case S.Ahead{+i, +neg}:
                      +hs = {LU.shu.head(1n+g, s, Nil{}, h) : {Nat.is_lt(Shape.sp_left(s), 1n+g) == True{} : Bool}}
                      +B = {S.val(b) : Nat}
                      +R = {Shape.sp_reads(1n+g, i, [s], B) : List<&2, S.St>}
                      +P = {Shape.sp_ahead(neg, R, s) : List<&2, S.St>}
                      +X = {S.seek(U, S.Want{s}, i, b, S.FEnd{}, False{}) : Maybe<&2, S.St>}
                      +m = {S.ahead.at(neg, X, s) : Maybe<&2, S.St>}
                      +M = {S.seek(U, S.want(m), t, S.BAfter{b, i}, K, e) : Maybe<&2, S.St>}
                      +hX = {shk.seek(U, S.Want{s}, 1n+g, i, b, S.FEnd{}, False{}, h) : {X == Shape.sp_head(R) : Maybe<&2, S.St>}}
                      +hm = {Equal.trans(List<&2, S.St>, S.m2l(m), S.m2l(S.ahead.at(neg, Shape.sp_head(R), s)), P, Equal.cong(Maybe<&2, S.St>, List<&2, S.St>, z => S.m2l(S.ahead.at(neg, z, s)), X, Shape.sp_head(R), hX), shk.ahead1(neg, R, s)) : {S.m2l(m) == P : List<&2, S.St>}}
                      +v = {shk.via(M, 1n+g, m, t, S.BAfter{b, i}, K, e, P, shk.seek(U, S.want(m), 1n+g, t, S.BAfter{b, i}, K, e, shk.fits_m(1n+g, m, P, hm, LU.shu.ahead(neg, R, s, 1n+g, hs))), hm) : {M == shk.G(1n+g, K, e, t, Nat.add(B, S.ncaps(i)), P) : Maybe<&2, S.St>}}
                      shk.fin(M, g, K, e, t, Nat.add(B, Shape.sp_ncaps(i)), P, S.Ahead{i, neg} <> t, B, Equal.trans(Maybe<&2, S.St>, M, shk.G(1n+g, K, e, t, Nat.add(B, S.ncaps(i)), P), shk.G(1n+g, K, e, t, Nat.add(B, Shape.sp_ncaps(i)), P), v, shk.G_base(1n+g, K, e, t, Nat.add(B, S.ncaps(i)), Nat.add(B, Shape.sp_ncaps(i)), P, shk.ncaps(B, i))))
