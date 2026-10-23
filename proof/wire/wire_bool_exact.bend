# eukhe: the proof of LAW wire_bool_exact

import Base
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../base/bool/misc.bend as LBoolMisc

def wr_lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  LBoolMisc.wr_absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e))

def wr_gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  LBoolMisc.wr_absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), GT{}, EQ{}, e))

def wr_cmp_eq_fin(-p: Nat, -at: Word(p), -bt: Word(p), t: Cmp, +ab: Bool, +bb: Bool,
  et: {Word.cmp(p, at, bt) == t : Cmp},
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match t:
    case LT{}:
      wr_lt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case GT{}:
      wr_gt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt, rec(et))
        case False{} True{}:
          wr_lt_eq({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, e)
        case True{} False{}:
          wr_gt_eq({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, e)
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt, rec(et))

# words that compare EQ are the same word (u32_order: Word.cmp_eq)
def wr_word_cmp_eq(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e => wr_cmp_eq_fin(p, at, bt, Word.cmp(p, at, bt), ab, bb, {==},
            wr_word_cmp_eq(p, at, bt), e)

# U32 values that compare EQ are equal (u32_order: cmp_eq)
def wr_cmp_eq(+a: U32, +b: U32) -> {U32.cmp(a, b) == EQ{} : Cmp} -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      e => Equal.cong(Word(32n), U32, w => U32{w}, x, y, wr_word_cmp_eq(32n, x, y)(e))

def wr_sound_fin(+a: U32, +b: U32, t: Cmp, et: {U32.cmp(a, b) == t : Cmp},
  e: {Cmp.is_eq(t) == True{} : Bool}) -> {a == b : U32}:
  match t:
    case LT{}:
      LBoolMisc.wr_absurd({a == b : U32}, e)
    case EQ{}:
      wr_cmp_eq(a, b)(et)
    case GT{}:
      LBoolMisc.wr_absurd({a == b : U32}, e)

# U32.is_eq is real equality (u32_order: eq_sound)
def wr_eq_sound(+a: U32, +b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  wr_sound_fin(a, b, U32.cmp(a, b), {==}, e)

# Bool
# ----

# what a Bool decoder answer says about its input s
def wr_pb(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def wr_bool_pick(+x: U32, +t: String, p: Bool, ep: {U32.is_eq(x, 84) == p : Bool},
  q: Bool, eq: {U32.is_eq(x, 70) == q : Bool}) -> wr_pb(SCon{Chr{x}, t}, Wr.get_bool.pick(p, q, t)):
  match p:
    case True{}:
      %Equal.sym(U32, x, 84, wr_eq_sound(x, 84, ep)) : {SCon{Chr{_}, t} == SCon{'T', t} : String}
      {==}
    case False{}:
      match q:
        case True{}:
          %Equal.sym(U32, x, 70, wr_eq_sound(x, 70, eq)) : {SCon{Chr{_}, t} == SCon{'F', t} : String}
          {==}
        case False{}:
          Unit{}

# every Bool the decoder reads is the encoding of what it answers
def wr_bool_spec(s: String) -> wr_pb(s, Wr.get_bool(s)):
  match s:
    case SNil{}:
      Unit{}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          wr_bool_pick(x, t, U32.is_eq(x, 84), {==}, U32.is_eq(x, 70), {==})

def Wire.wire_bool_exact(s, b, rest, h):
  %h : wr_pb(s, _)
  wr_bool_spec(s)
