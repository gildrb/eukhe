# eukhe: equal codes are equal chars (U32.is_eq is real equality: the
# argument of proof/wire/wire_bool_exact.bend, wr_eq_sound), every char
# equals itself, and the spec's text comparison (Shape.sp_text_eq) on
# chars and texts.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ./fuel.bend as LU

def shq.lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  LU.shu.absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e))

def shq.gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  LU.shu.absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), GT{}, EQ{}, e))

def shq.cmp_eq_fin(-p: Nat, -at: Word(p), -bt: Word(p), t: Cmp, +ab: Bool, +bb: Bool,
  et: {Word.cmp(p, at, bt) == t : Cmp},
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match t:
    case LT{}:
      shq.lt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case GT{}:
      shq.gt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt, rec(et))
        case False{} True{}:
          shq.lt_eq({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, e)
        case True{} False{}:
          shq.gt_eq({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, e)
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt, rec(et))

def shq.word_cmp_eq(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e => shq.cmp_eq_fin(p, at, bt, Word.cmp(p, at, bt), ab, bb, {==},
            shq.word_cmp_eq(p, at, bt), e)

def shq.cmp_eq(+a: U32, +b: U32) -> {U32.cmp(a, b) == EQ{} : Cmp} -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      e => Equal.cong(Word(32n), U32, w => U32{w}, x, y, shq.word_cmp_eq(32n, x, y)(e))

def shq.sound_fin(+a: U32, +b: U32, t: Cmp, et: {U32.cmp(a, b) == t : Cmp},
  e: {Cmp.is_eq(t) == True{} : Bool}) -> {a == b : U32}:
  match t:
    case LT{}:
      LU.shu.absurd({a == b : U32}, e)
    case EQ{}:
      shq.cmp_eq(a, b)(et)
    case GT{}:
      LU.shu.absurd({a == b : U32}, e)

# U32.is_eq is real equality
def shq.eq_sound(+a: U32, +b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  shq.sound_fin(a, b, U32.cmp(a, b), {==}, e)

def shq.bool_cmp(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# every word equals itself
def shq.word_refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{+ab, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, shq.word_refl(p, at)) : {Word.cmp.fin(ab, ab, _) == EQ{} : Cmp}
          shq.bool_cmp(ab)

def shq.u32_refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, shq.word_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# every char equals itself, with or without case
def shq.ch_refl(ci: Bool, x: Char) -> {Shape.sp_ch_eq(ci, x, x) == True{} : Bool}:
  match ci:
    case True{}:
      match x:
        case Chr{+a}:
          shq.u32_refl(Shape.sp_small(a))
    case False{}:
      match x:
        case Chr{+a}:
          shq.u32_refl(a)

# chars equal as the spec compares them without case are the same char
def shq.ch_sound(x: Char, y: Char, h: {Shape.sp_ch_eq(False{}, x, y) == True{} : Bool}) -> {x == y : Char}:
  match x y:
    case Chr{+a} Chr{+b}:
      Equal.cong(U32, Char, c => Chr{c}, a, b, shq.eq_sound(a, b, h))

def shq.text_refl(+ci: Bool, u: String) -> {Shape.sp_text_eq(ci, u, u) == True{} : Bool}:
  match u:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      LU.shu.and_t(Shape.sp_ch_eq(ci, x, x), Shape.sp_text_eq(ci, t, t), shq.ch_refl(ci, x), shq.text_refl(ci, t))

def shq.text_sound(u: String, v: String, +h: {Shape.sp_text_eq(False{}, u, v) == True{} : Bool}) -> {u == v : String}:
  match u v:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, b}:
      LU.shu.absurd({SNil{} == SCon{y, b} : String}, h)
    case SCon{x, a} SNil{}:
      LU.shu.absurd({SCon{x, a} == SNil{} : String}, h)
    case SCon{+x, +a} SCon{+y, +b}:
      +hc = {LU.shu.and_l(Shape.sp_ch_eq(False{}, x, y), Shape.sp_text_eq(False{}, a, b), h) : {Shape.sp_ch_eq(False{}, x, y) == True{} : Bool}}
      +ht = {LU.shu.and_r(Shape.sp_ch_eq(False{}, x, y), Shape.sp_text_eq(False{}, a, b), h) : {Shape.sp_text_eq(False{}, a, b) == True{} : Bool}}
      %Equal.sym(Char, x, y, shq.ch_sound(x, y, hc)) : {SCon{_, a} == SCon{y, b} : String}
      Equal.cong(String, String, w => SCon{y, w}, a, b, shq.text_sound(a, b, ht))
