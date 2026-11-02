# eukhe: the split of one piece that reads no inner pieces (laws/shape/match.bend
# R6) reaches exactly that piece's readings (R4): each leaf's part, both
# ways; and a split from no place reaches no place.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../base.bend as LA
import ./has.bend as LH
import ./fuel.bend as LU
import ./chars.bend as LQ

# Maybe
# -----

def shp.MIf(m: Maybe<&2, S.St>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def shp.none_some(-G: Type, -b: S.St, e: {None{} == Some{b} : Maybe<&2, S.St>}) -> G:
  %e : shp.MIf(_, G)
  Unit{}

def shp.get(m: Maybe<&2, S.St>, d: S.St) -> S.St:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def shp.some_inj(+a: S.St, -b: S.St, e: {Some{a} == Some{b} : Maybe<&2, S.St>}) -> {a == b : S.St}:
  Equal.cong(Maybe<&2, S.St>, S.St, m => shp.get(m, a), Some{a}, Some{b}, e)

def shp.when_t(b: Bool, -m: Maybe<&2, S.St>, -z: S.St, h: {Shape.sp_when(b, m) == Some{z} : Maybe<&2, S.St>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      shp.none_some({False{} == True{} : Bool}, z, h)

def shp.when_m(b: Bool, -m: Maybe<&2, S.St>, -z: S.St, h: {Shape.sp_when(b, m) == Some{z} : Maybe<&2, S.St>}) -> {m == Some{z} : Maybe<&2, S.St>}:
  match b:
    case True{}:
      h
    case False{}:
      shp.none_some({m == Some{z} : Maybe<&2, S.St>}, z, h)

def shp.when_none(b: Bool) -> {Shape.sp_when(b, None{}) == None{} : Maybe<&2, S.St>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def shp.when_true(-b: Bool, -m: Maybe<&2, S.St>, e: {b == True{} : Bool}) -> {Shape.sp_when(b, m) == m : Maybe<&2, S.St>}:
  %Equal.sym(Bool, b, True{}, e) : {Shape.sp_when(_, m) == m : Maybe<&2, S.St>}
  {==}

def shp.if_t(b: Bool, -xs: List<&2, S.St>, -z: S.St, h: Shape.sp_has(z, Shape.sp_if(b, xs))) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match h:

def shp.if_has(b: Bool, -xs: List<&2, S.St>, -z: S.St, h: Shape.sp_has(z, Shape.sp_if(b, xs))) -> Shape.sp_has(z, xs):
  match b:
    case True{}:
      h
    case False{}:
      match h:

def shp.if_head(b: Bool, -xs: List<&2, S.St>, -z: S.St, h: {Shape.sp_head(Shape.sp_if(b, xs)) == Some{z} : Maybe<&2, S.St>}) -> {Shape.sp_head(xs) == Some{z} : Maybe<&2, S.St>}:
  match b:
    case True{}:
      h
    case False{}:
      shp.none_some({Shape.sp_head(xs) == Some{z} : Maybe<&2, S.St>}, z, h)

def shp.if_head_t(b: Bool, -xs: List<&2, S.St>, -z: S.St, h: {Shape.sp_head(Shape.sp_if(b, xs)) == Some{z} : Maybe<&2, S.St>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      shp.none_some({False{} == True{} : Bool}, z, h)

def shp.if_true(-b: Bool, -xs: List<&2, S.St>, e: {b == True{} : Bool}) -> {Shape.sp_if(b, xs) == xs : List<&2, S.St>}:
  %Equal.sym(Bool, b, True{}, e) : {Shape.sp_if(_, xs) == xs : List<&2, S.St>}
  {==}

# the head of a list is one of its places
def shp.head_has(xs: List<&2, S.St>, -z: S.St, h: {Shape.sp_head(xs) == Some{z} : Maybe<&2, S.St>}) -> Shape.sp_has(z, xs):
  match xs:
    case Nil{}:
      shp.none_some(Shape.sp_has(z, Nil{}), z, h)
    case +x <> t:
      Inl{shp.some_inj(x, z, h)}

# Lit, Fold: reading chars gives at most one place
def shp.eat_head(u: String, +ci: Bool, s: S.St, -z: S.St, +h: Shape.sp_has(z, Shape.sp_eat(u, ci, s))) -> {Shape.sp_head(Shape.sp_eat(u, ci, s)) == Some{z} : Maybe<&2, S.St>}:
  match u:
    case SNil{}:
      Equal.cong(S.St, Maybe<&2, S.St>, x => Some{x}, s, z, LH.shh.single(z, s, h))
    case SCon{+y, +v}:
      match s:
        case S.St{+pos, +left, +word, +rest, +caps}:
          match rest:
            case SNil{}:
              match h:
            case SCon{+x, +t}:
              +b = {Shape.sp_ch_eq(ci, x, y) : Bool}
              +s2 = {S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps} : S.St}
              +e = {shp.if_t(b, Shape.sp_eat(v, ci, s2), z, h) : {b == True{} : Bool}}
              %Equal.sym(List<&2, S.St>, Shape.sp_if(b, Shape.sp_eat(v, ci, s2)), Shape.sp_eat(v, ci, s2), shp.if_true(b, Shape.sp_eat(v, ci, s2), e)) : {Shape.sp_head(_) == Some{z} : Maybe<&2, S.St>}
              shp.eat_head(v, ci, s2, z, shp.if_has(b, Shape.sp_eat(v, ci, s2), z, h))

# Lit: a part equal to the text is the place after it
def shp.lit_c(+u: String, +v: String, +s: S.St, -z: S.St, +h: {Shape.sp_when(Shape.sp_text_eq(False{}, u, v), Shape.sp_go_on(u, Some{s})) == Some{z} : Maybe<&2, S.St>}) -> Shape.sp_has(z, Shape.sp_eat(v, False{}, s)):
  +b = {Shape.sp_text_eq(False{}, u, v) : Bool}
  +e = {LQ.shq.text_sound(u, v, shp.when_t(b, Shape.sp_go_on(u, Some{s}), z, h)) : {u == v : String}}
  +hm = {shp.when_m(b, Shape.sp_go_on(u, Some{s}), z, h) : {Shape.sp_head(Shape.sp_eat(u, False{}, s)) == Some{z} : Maybe<&2, S.St>}}
  %e : Shape.sp_has(z, Shape.sp_eat(_, False{}, s))
  shp.head_has(Shape.sp_eat(u, False{}, s), z, hm)

def shp.lit_s(+v: String, +s: S.St, -z: S.St, h: Shape.sp_has(z, Shape.sp_eat(v, False{}, s))) -> {Shape.sp_when(Shape.sp_text_eq(False{}, v, v), Shape.sp_go_on(v, Some{s})) == Some{z} : Maybe<&2, S.St>}:
  %Equal.sym(Maybe<&2, S.St>, Shape.sp_when(Shape.sp_text_eq(False{}, v, v), Shape.sp_go_on(v, Some{s})), Shape.sp_go_on(v, Some{s}), shp.when_true(Shape.sp_text_eq(False{}, v, v), Shape.sp_go_on(v, Some{s}), LQ.shq.text_refl(False{}, v))) : {_ == Some{z} : Maybe<&2, S.St>}
  shp.eat_head(v, False{}, s, z, h)

# Fold: a part equal to the pattern once capitals are read as small, the
# text going on with it, reaches the Fold's reading
def shp.fold_c(u: String, v: String, s: S.St, -z: S.St, +h1: {Shape.sp_text_eq(True{}, u, v) == True{} : Bool}, +h2: {Shape.sp_head(Shape.sp_eat(u, False{}, s)) == Some{z} : Maybe<&2, S.St>}) -> Shape.sp_has(z, Shape.sp_eat(v, True{}, s)):
  match u v:
    case SNil{} SNil{}:
      Inl{shp.some_inj(s, z, h2)}
    case SNil{} SCon{y, b}:
      LU.shu.absurd(Shape.sp_has(z, Shape.sp_eat(SCon{y, b}, True{}, s)), h1)
    case SCon{x, a} SNil{}:
      LU.shu.absurd(Shape.sp_has(z, Shape.sp_eat(SNil{}, True{}, s)), h1)
    case SCon{+x2, +a} SCon{+y, +b}:
      match s:
        case S.St{+pos, +left, +word, +rest, +caps}:
          match rest:
            case SNil{}:
              shp.none_some(Shape.sp_has(z, Shape.sp_eat(SCon{y, b}, True{}, S.St{pos, left, word, SNil{}, caps})), z, h2)
            case SCon{+x, +t}:
              +s2 = {S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps} : S.St}
              +ex = {LQ.shq.ch_sound(x, x2, shp.if_head_t(Shape.sp_ch_eq(False{}, x, x2), Shape.sp_eat(a, False{}, s2), z, h2)) : {x == x2 : Char}}
              +c2 = {LU.shu.and_l(Shape.sp_ch_eq(True{}, x2, y), Shape.sp_text_eq(True{}, a, b), h1) : {Shape.sp_ch_eq(True{}, x2, y) == True{} : Bool}}
              +c1 = {Equal.trans(Bool, Shape.sp_ch_eq(True{}, x, y), Shape.sp_ch_eq(True{}, x2, y), True{}, Equal.cong(Char, Bool, w => Shape.sp_ch_eq(True{}, w, y), x, x2, ex), c2) : {Shape.sp_ch_eq(True{}, x, y) == True{} : Bool}}
              %Equal.sym(List<&2, S.St>, Shape.sp_if(Shape.sp_ch_eq(True{}, x, y), Shape.sp_eat(b, True{}, s2)), Shape.sp_eat(b, True{}, s2), shp.if_true(Shape.sp_ch_eq(True{}, x, y), Shape.sp_eat(b, True{}, s2), c1)) : Shape.sp_has(z, _)
              shp.fold_c(a, b, s2, z, LU.shu.and_r(Shape.sp_ch_eq(True{}, x2, y), Shape.sp_text_eq(True{}, a, b), h1), shp.if_head(Shape.sp_ch_eq(False{}, x, x2), Shape.sp_eat(a, False{}, s2), z, h2))

# Fold, the other way: the chars the text goes on with are such a part
def shp.fold_s.fin(+x: Char, -y: Char, -v: String, +t: String, +pos: Nat, +left: Nat, +word: Bool, +caps: List<&2, Maybe<&2, S.Got>>, -z: S.St, +c: {Shape.sp_ch_eq(True{}, x, y) == True{} : Bool}, w: &u: String -> ({Shape.sp_text_eq(True{}, u, v) == True{} : Bool} & {Shape.sp_head(Shape.sp_eat(u, False{}, S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps})) == Some{z} : Maybe<&2, S.St>})) -> &u: String -> ({Shape.sp_text_eq(True{}, u, SCon{y, v}) == True{} : Bool} & {Shape.sp_head(Shape.sp_eat(u, False{}, S.St{pos, left, word, SCon{x, t}, caps})) == Some{z} : Maybe<&2, S.St>}):
  (+u, hp) = w
  (e1, e2) = hp
  +s2 = {S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps} : S.St}
  +a = {Shape.sp_if(Shape.sp_ch_eq(False{}, x, x), Shape.sp_eat(u, False{}, s2)) : List<&2, S.St>}
  (SCon{x, u}, (LU.shu.and_t(Shape.sp_ch_eq(True{}, x, y), Shape.sp_text_eq(True{}, u, v), c, e1), Equal.trans(Maybe<&2, S.St>, Shape.sp_head(a), Shape.sp_head(Shape.sp_eat(u, False{}, s2)), Some{z}, Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, xs => Shape.sp_head(xs), a, Shape.sp_eat(u, False{}, s2), shp.if_true(Shape.sp_ch_eq(False{}, x, x), Shape.sp_eat(u, False{}, s2), LQ.shq.ch_refl(False{}, x))), e2)))

def shp.fold_s(v: String, s: S.St, -z: S.St, +h: Shape.sp_has(z, Shape.sp_eat(v, True{}, s))) -> &u: String -> ({Shape.sp_text_eq(True{}, u, v) == True{} : Bool} & {Shape.sp_head(Shape.sp_eat(u, False{}, s)) == Some{z} : Maybe<&2, S.St>}):
  match v:
    case SNil{}:
      (SNil{}, ({==}, Equal.cong(S.St, Maybe<&2, S.St>, x => Some{x}, s, z, LH.shh.single(z, s, h))))
    case SCon{+y, +b}:
      match s:
        case S.St{+pos, +left, +word, +rest, +caps}:
          match rest:
            case SNil{}:
              match h:
            case SCon{+x, +t}:
              +s2 = {S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps} : S.St}
              +c = {Shape.sp_ch_eq(True{}, x, y) : Bool}
              shp.fold_s.fin(x, y, b, t, pos, left, word, caps, z, shp.if_t(c, Shape.sp_eat(b, True{}, s2), z, h), shp.fold_s(b, s2, z, shp.if_has(c, Shape.sp_eat(b, True{}, s2), z, h)))

# Nat bounds of a run
# -------------------

def shp.le_dec(a: Nat, -b: Nat, h: {Nat.is_le(Shape.sp_dec(a), b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      h

def shp.le_back(a: Nat, b: Nat, h: {Nat.is_le(a, 1n+b) == True{} : Bool}) -> {Nat.is_le(Shape.sp_dec(a), b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      h

def shp.le0(a: Nat, h: {Nat.is_le(a, 0n) == True{} : Bool}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      LU.shu.absurd({1n+p == 0n : Nat}, h)

def shp.am_up(-n: Nat, max: Maybe<&2, Nat>, hr: {Shape.sp_room(max) == True{} : Bool}, h: {Shape.sp_at_most(n, Shape.sp_less(max)) == True{} : Bool}) -> {Shape.sp_at_most(1n+n, max) == True{} : Bool}:
  match max:
    case None{}:
      {==}
    case Some{k}:
      match k:
        case 0n:
          LU.shu.absurd({Shape.sp_at_most(1n+n, Some{0n}) == True{} : Bool}, hr)
        case 1n+j:
          h

def shp.am_room(-n: Nat, max: Maybe<&2, Nat>, h: {Shape.sp_at_most(1n+n, max) == True{} : Bool}) -> {Shape.sp_room(max) == True{} : Bool}:
  match max:
    case None{}:
      {==}
    case Some{k}:
      match k:
        case 0n:
          LU.shu.absurd({Shape.sp_room(Some{0n}) == True{} : Bool}, h)
        case 1n+j:
          {==}

def shp.am_down(-n: Nat, max: Maybe<&2, Nat>, h: {Shape.sp_at_most(1n+n, max) == True{} : Bool}) -> {Shape.sp_at_most(n, Shape.sp_less(max)) == True{} : Bool}:
  match max:
    case None{}:
      {==}
    case Some{k}:
      match k:
        case 0n:
          LU.shu.absurd({Shape.sp_at_most(n, Shape.sp_less(Some{0n})) == True{} : Bool}, h)
        case 1n+j:
          h

def shp.am0(max: Maybe<&2, Nat>) -> {Shape.sp_at_most(0n, max) == True{} : Bool}:
  match max:
    case None{}:
      {==}
    case Some{k}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}

def shp.zero_min(min: Nat, -x: S.St, -z: S.St, h: Shape.sp_has(z, Shape.sp_zero(min, x))) -> {min == 0n : Nat}:
  match min:
    case 0n:
      {==}
    case 1n+m:
      match h:

def shp.zero_is(min: Nat, -x: S.St, -z: S.St, h: Shape.sp_has(z, Shape.sp_zero(min, x))) -> {x == z : S.St}:
  match min:
    case 0n:
      LH.shh.single(z, x, h)
    case 1n+m:
      match h:

# Run: a run read from the place is a part of at least min and at most max
# chars of the class
def shp.run_s.empty(+c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +x: S.St, -z: S.St, +h: Shape.sp_has(z, Shape.sp_zero(min, x))) -> {Shape.sp_part_run(c, min, max, SNil{}, Some{x}) == Some{z} : Maybe<&2, S.St>}:
  %Equal.sym(Nat, min, 0n, shp.zero_min(min, x, z, h)) : {Shape.sp_part_run(c, _, max, SNil{}, Some{x}) == Some{z} : Maybe<&2, S.St>}
  %Equal.sym(Bool, Shape.sp_at_most(0n, max), True{}, shp.am0(max)) : {Shape.sp_when(Bool.and(True{}, Bool.and(True{}, _)), Some{x}) == Some{z} : Maybe<&2, S.St>}
  Equal.cong(S.St, Maybe<&2, S.St>, w => Some{w}, x, z, shp.zero_is(min, x, z, h))

def shp.run_s.fin(+x: Char, +t: String, +c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +pos: Nat, +left: Nat, +word: Bool, +caps: List<&2, Maybe<&2, S.Got>>, -z: S.St, +hc: {Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)) == True{} : Bool}, w: &u: String -> {Shape.sp_part_run(c, Shape.sp_dec(min), Shape.sp_less(max), u, Some{S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps}}) == Some{z} : Maybe<&2, S.St>}) -> &u: String -> {Shape.sp_part_run(c, min, max, u, Some{S.St{pos, left, word, SCon{x, t}, caps}}) == Some{z} : Maybe<&2, S.St>}:
  (+u, e0) = w
  +s2 = {S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps} : S.St}
  +e = {e0 : {Shape.sp_part_run(c, Shape.sp_dec(min), Shape.sp_less(max), u, Some{s2}) == Some{z} : Maybe<&2, S.St>}}
  +n = {String.length(u) : Nat}
  +b2 = {Bool.and(Shape.sp_all_cls(c, u), Bool.and(Nat.is_le(Shape.sp_dec(min), n), Shape.sp_at_most(n, Shape.sp_less(max)))) : Bool}
  +ec = {shp.when_t(b2, Shape.sp_go_on(u, Some{s2}), z, e) : {b2 == True{} : Bool}}
  +eg = {shp.when_m(b2, Shape.sp_go_on(u, Some{s2}), z, e) : {Shape.sp_go_on(u, Some{s2}) == Some{z} : Maybe<&2, S.St>}}
  +r1 = {Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)) : Bool}
  +q = {Bool.and(Nat.is_le(Shape.sp_dec(min), n), Shape.sp_at_most(n, Shape.sp_less(max))) : Bool}
  +hq = {LU.shu.and_r(Shape.sp_all_cls(c, u), q, ec) : {q == True{} : Bool}}
  +hall = {LU.shu.and_t(Shape.sp_cls(c, x), Shape.sp_all_cls(c, u), LU.shu.and_r(Shape.sp_room(max), Shape.sp_cls(c, x), hc), LU.shu.and_l(Shape.sp_all_cls(c, u), q, ec)) : {Shape.sp_all_cls(c, SCon{x, u}) == True{} : Bool}}
  +hle = {shp.le_dec(min, n, LU.shu.and_l(Nat.is_le(Shape.sp_dec(min), n), Shape.sp_at_most(n, Shape.sp_less(max)), hq)) : {Nat.is_le(min, 1n+n) == True{} : Bool}}
  +ham = {shp.am_up(n, max, LU.shu.and_l(Shape.sp_room(max), Shape.sp_cls(c, x), hc), LU.shu.and_r(Nat.is_le(Shape.sp_dec(min), n), Shape.sp_at_most(n, Shape.sp_less(max)), hq)) : {Shape.sp_at_most(1n+n, max) == True{} : Bool}}
  +cond = {Bool.and(Shape.sp_all_cls(c, SCon{x, u}), Bool.and(Nat.is_le(min, 1n+n), Shape.sp_at_most(1n+n, max))) : Bool}
  +hcond = {LU.shu.and_t(Shape.sp_all_cls(c, SCon{x, u}), Bool.and(Nat.is_le(min, 1n+n), Shape.sp_at_most(1n+n, max)), hall, LU.shu.and_t(Nat.is_le(min, 1n+n), Shape.sp_at_most(1n+n, max), hle, ham)) : {cond == True{} : Bool}}
  +a = {Shape.sp_if(Shape.sp_ch_eq(False{}, x, x), Shape.sp_eat(u, False{}, s2)) : List<&2, S.St>}
  +ego = {Equal.trans(Maybe<&2, S.St>, Shape.sp_head(a), Shape.sp_go_on(u, Some{s2}), Some{z}, Equal.cong(List<&2, S.St>, Maybe<&2, S.St>, xs => Shape.sp_head(xs), a, Shape.sp_eat(u, False{}, s2), shp.if_true(Shape.sp_ch_eq(False{}, x, x), Shape.sp_eat(u, False{}, s2), LQ.shq.ch_refl(False{}, x))), eg) : {Shape.sp_head(a) == Some{z} : Maybe<&2, S.St>}}
  (SCon{x, u}, Equal.trans(Maybe<&2, S.St>, Shape.sp_when(cond, Shape.sp_head(a)), Shape.sp_head(a), Some{z}, shp.when_true(cond, Shape.sp_head(a), hcond), ego))

def shp.run_s.go(+x: Char, +t: String, +c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +pos: Nat, +left: Nat, +word: Bool, +caps: List<&2, Maybe<&2, S.Got>>, -z: S.St, e: Shape.sp_has(z, Shape.sp_if(Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)), Shape.sp_run.go(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps))) | Shape.sp_has(z, Shape.sp_zero(min, S.St{pos, left, word, SCon{x, t}, caps})), ih: Shape.sp_has(z, Shape.sp_run.go(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps)) -> &u: String -> {Shape.sp_part_run(c, Shape.sp_dec(min), Shape.sp_less(max), u, Some{S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps}}) == Some{z} : Maybe<&2, S.St>}) -> &u: String -> {Shape.sp_part_run(c, min, max, u, Some{S.St{pos, left, word, SCon{x, t}, caps}}) == Some{z} : Maybe<&2, S.St>}:
  match e:
    case Inl{+h1}:
      +r1 = {Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)) : Bool}
      +X = {Shape.sp_run.go(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps) : List<&2, S.St>}
      shp.run_s.fin(x, t, c, min, max, pos, left, word, caps, z, shp.if_t(r1, X, z, h1), ih(shp.if_has(r1, X, z, h1)))
    case Inr{+h2}:
      (SNil{}, shp.run_s.empty(c, min, max, S.St{pos, left, word, SCon{x, t}, caps}, z, h2))

def shp.run_s(rest: String, +c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +pos: Nat, +left: Nat, +word: Bool, +caps: List<&2, Maybe<&2, S.Got>>, -z: S.St, h: Shape.sp_has(z, Shape.sp_run.go(rest, c, min, max, pos, left, word, caps))) -> &u: String -> {Shape.sp_part_run(c, min, max, u, Some{S.St{pos, left, word, rest, caps}}) == Some{z} : Maybe<&2, S.St>}:
  match rest:
    case SNil{}:
      (SNil{}, shp.run_s.empty(c, min, max, S.St{pos, left, word, SNil{}, caps}, z, h))
    case SCon{+x, +t}:
      +r1 = {Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)) : Bool}
      +X = {Shape.sp_run.go(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps) : List<&2, S.St>}
      shp.run_s.go(x, t, c, min, max, pos, left, word, caps, z, LH.shh.app_split(z, Shape.sp_if(r1, X), Shape.sp_zero(min, S.St{pos, left, word, SCon{x, t}, caps}), h), k => shp.run_s(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps, z, k))

def shp.run_c.zero(min: Nat, +x: S.St, -z: S.St, e: {min == 0n : Nat}, ex: {x == z : S.St}) -> Shape.sp_has(z, Shape.sp_zero(min, x)):
  %Equal.sym(Nat, min, 0n, e) : Shape.sp_has(z, Shape.sp_zero(_, x))
  Inl{ex}

# Run, the other way: a part of at least min and at most max chars of the
# class is one of the run's readings
def shp.run_c(rest: String, +c: S.Cls, +min: Nat, +max: Maybe<&2, Nat>, +pos: Nat, +left: Nat, +word: Bool, +caps: List<&2, Maybe<&2, S.Got>>, u: String, -z: S.St, +h: {Shape.sp_part_run(c, min, max, u, Some{S.St{pos, left, word, rest, caps}}) == Some{z} : Maybe<&2, S.St>}) -> Shape.sp_has(z, Shape.sp_run.go(rest, c, min, max, pos, left, word, caps)):
  match rest:
    case SNil{}:
      match u:
        case SNil{}:
          +x = {S.St{pos, left, word, SNil{}, caps} : S.St}
          +b = {Bool.and(True{}, Bool.and(Nat.is_le(min, 0n), Shape.sp_at_most(0n, max))) : Bool}
          +hb = {shp.when_t(b, Some{x}, z, h) : {b == True{} : Bool}}
          +em = {shp.le0(min, LU.shu.and_l(Nat.is_le(min, 0n), Shape.sp_at_most(0n, max), hb)) : {min == 0n : Nat}}
          %Equal.sym(Nat, min, 0n, em) : Shape.sp_has(z, Shape.sp_zero(_, x))
          Inl{shp.some_inj(x, z, shp.when_m(b, Some{x}, z, h))}
        case SCon{+y, +v}:
          +b = {Bool.and(Shape.sp_all_cls(c, SCon{y, v}), Bool.and(Nat.is_le(min, 1n+String.length(v)), Shape.sp_at_most(1n+String.length(v), max))) : Bool}
          shp.none_some(Shape.sp_has(z, Shape.sp_run.go(SNil{}, c, min, max, pos, left, word, caps)), z, Equal.trans(Maybe<&2, S.St>, None{}, Shape.sp_when(b, None{}), Some{z}, Equal.sym(Maybe<&2, S.St>, Shape.sp_when(b, None{}), None{}, shp.when_none(b)), h))
    case SCon{+x, +t}:
      match u:
        case SNil{}:
          +r1 = {Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)) : Bool}
          +X = {Shape.sp_run.go(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps) : List<&2, S.St>}
          +here = {S.St{pos, left, word, SCon{x, t}, caps} : S.St}
          +b = {Bool.and(True{}, Bool.and(Nat.is_le(min, 0n), Shape.sp_at_most(0n, max))) : Bool}
          +hb = {shp.when_t(b, Some{here}, z, h) : {b == True{} : Bool}}
          +em = {shp.le0(min, LU.shu.and_l(Nat.is_le(min, 0n), Shape.sp_at_most(0n, max), hb)) : {min == 0n : Nat}}
          LH.shh.app_r(z, Shape.sp_if(r1, X), Shape.sp_zero(min, here), shp.run_c.zero(min, here, z, em, shp.some_inj(here, z, shp.when_m(b, Some{here}, z, h))))
        case SCon{+y, +v}:
          +r1 = {Bool.and(Shape.sp_room(max), Shape.sp_cls(c, x)) : Bool}
          +X = {Shape.sp_run.go(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps) : List<&2, S.St>}
          +here = {S.St{pos, left, word, SCon{x, t}, caps} : S.St}
          +n = {String.length(v) : Nat}
          +s2 = {S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps} : S.St}
          +b = {Bool.and(Shape.sp_all_cls(c, SCon{y, v}), Bool.and(Nat.is_le(min, 1n+n), Shape.sp_at_most(1n+n, max))) : Bool}
          +hb = {shp.when_t(b, Shape.sp_go_on(SCon{y, v}, Some{here}), z, h) : {b == True{} : Bool}}
          +hg = {shp.when_m(b, Shape.sp_go_on(SCon{y, v}, Some{here}), z, h) : {Shape.sp_head(Shape.sp_if(Shape.sp_ch_eq(False{}, x, y), Shape.sp_eat(v, False{}, s2))) == Some{z} : Maybe<&2, S.St>}}
          +exy = {LQ.shq.ch_sound(x, y, shp.if_head_t(Shape.sp_ch_eq(False{}, x, y), Shape.sp_eat(v, False{}, s2), z, hg)) : {x == y : Char}}
          +hcl = {LU.shu.and_l(Shape.sp_all_cls(c, SCon{y, v}), Bool.and(Nat.is_le(min, 1n+n), Shape.sp_at_most(1n+n, max)), hb) : {Shape.sp_all_cls(c, SCon{y, v}) == True{} : Bool}}
          +hlm = {LU.shu.and_r(Shape.sp_all_cls(c, SCon{y, v}), Bool.and(Nat.is_le(min, 1n+n), Shape.sp_at_most(1n+n, max)), hb) : {Bool.and(Nat.is_le(min, 1n+n), Shape.sp_at_most(1n+n, max)) == True{} : Bool}}
          +hcy = {LU.shu.and_l(Shape.sp_cls(c, y), Shape.sp_all_cls(c, v), hcl) : {Shape.sp_cls(c, y) == True{} : Bool}}
          +hcx = {Equal.trans(Bool, Shape.sp_cls(c, x), Shape.sp_cls(c, y), True{}, Equal.cong(Char, Bool, w => Shape.sp_cls(c, w), x, y, exy), hcy) : {Shape.sp_cls(c, x) == True{} : Bool}}
          +ham = {LU.shu.and_r(Nat.is_le(min, 1n+n), Shape.sp_at_most(1n+n, max), hlm) : {Shape.sp_at_most(1n+n, max) == True{} : Bool}}
          +hr1 = {LU.shu.and_t(Shape.sp_room(max), Shape.sp_cls(c, x), shp.am_room(n, max, ham), hcx) : {r1 == True{} : Bool}}
          +b2 = {Bool.and(Shape.sp_all_cls(c, v), Bool.and(Nat.is_le(Shape.sp_dec(min), n), Shape.sp_at_most(n, Shape.sp_less(max)))) : Bool}
          +hb2 = {LU.shu.and_t(Shape.sp_all_cls(c, v), Bool.and(Nat.is_le(Shape.sp_dec(min), n), Shape.sp_at_most(n, Shape.sp_less(max))), LU.shu.and_r(Shape.sp_cls(c, y), Shape.sp_all_cls(c, v), hcl), LU.shu.and_t(Nat.is_le(Shape.sp_dec(min), n), Shape.sp_at_most(n, Shape.sp_less(max)), shp.le_back(min, n, LU.shu.and_l(Nat.is_le(min, 1n+n), Shape.sp_at_most(1n+n, max), hlm)), shp.am_down(n, max, ham))) : {b2 == True{} : Bool}}
          +h2 = {Equal.trans(Maybe<&2, S.St>, Shape.sp_when(b2, Shape.sp_go_on(v, Some{s2})), Shape.sp_go_on(v, Some{s2}), Some{z}, shp.when_true(b2, Shape.sp_go_on(v, Some{s2}), hb2), shp.if_head(Shape.sp_ch_eq(False{}, x, y), Shape.sp_eat(v, False{}, s2), z, hg)) : {Shape.sp_part_run(c, Shape.sp_dec(min), Shape.sp_less(max), v, Some{s2}) == Some{z} : Maybe<&2, S.St>}}
          %Equal.sym(List<&2, S.St>, Shape.sp_if(r1, X), X, shp.if_true(r1, X, hr1)) : Shape.sp_has(z, List.append(&2, S.St, _, Shape.sp_zero(min, here)))
          LH.shh.app_l(z, X, Shape.sp_zero(min, here), shp.run_c(t, c, Shape.sp_dec(min), Shape.sp_less(max), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps, v, z, h2))
