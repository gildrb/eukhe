# eukhe: lemmas of the refine_plan proofs about chars: Char.is_eq and
# U32.is_eq are equality, and an ASCII uppercase letter lowercases to a
# char other than `_`

import Base

def BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : BD(_, Unit, A)
  Unit{}

def absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  absurd(A, Equal.sym(Bool, False{}, True{}, e))

def lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), EQ{}, LT{}, Equal.sym(Cmp, LT{}, EQ{}, e)))

def gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), EQ{}, GT{}, Equal.sym(Cmp, GT{}, EQ{}, e)))

def cmp_eq_fin(-p: Nat, -at: Word(p), -bt: Word(p), t: Cmp, +ab: Bool, +bb: Bool,
  et: {Word.cmp(p, at, bt) == t : Cmp},
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match t:
    case LT{}:
      lt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case GT{}:
      gt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt, rec(et))
        case False{} True{}:
          lt_eq({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, e)
        case True{} False{}:
          gt_eq({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, e)
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt, rec(et))

def word_eq(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e => cmp_eq_fin(p, at, bt, Word.cmp(p, at, bt), ab, bb, {==}, word_eq(p, at, bt), e)

# 2, the high 27 bits of 65, 90 and 95
def up.two() -> Word(27n):
  WCon{False{}, WCon{True{}, Word.zero(25n)}}

# is_upper of a char whose high 27 bits compare t with 2
def up.U(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +t: Cmp) -> Bool:
  Bool.and(Cmp.is_ge(Word.cmp.fin(b0, True{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, False{}, Word.cmp.fin(b3, False{}, Word.cmp.fin(b4, False{}, t)))))), Cmp.is_le(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, True{}, Word.cmp.fin(b2, False{}, Word.cmp.fin(b3, True{}, Word.cmp.fin(b4, True{}, t)))))))

def up.C(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, y: Word(27n)) -> Char:
  Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, y}}}}}}}

def up.G(c: Char) -> Type:
  {Char.is_eq(Char.to_lower(c), '_') == False{} : Bool}

def up.bits(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool) -> {Char.is_upper(up.C(b0, b1, b2, b3, b4, up.two())) == True{} : Bool} -> up.G(up.C(b0, b1, b2, b3, b4, up.two())):
  match b0:
    case True{}:
      match b1:
        case True{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  match b4:
                    case True{}:
                      h => absurdF(up.G(up.C(True{}, True{}, True{}, True{}, True{}, up.two())), h)
                    case False{}:
                      h => {==}
                case False{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
            case False{}:
              match b3:
                case True{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
                case False{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
        case False{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
                case False{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
            case False{}:
              match b3:
                case True{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
                case False{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
    case False{}:
      match b1:
        case True{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
                case False{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
            case False{}:
              match b3:
                case True{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
                case False{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
        case False{}:
          match b2:
            case True{}:
              match b3:
                case True{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
                case False{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
            case False{}:
              match b3:
                case True{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}
                case False{}:
                  match b4:
                    case True{}:
                      h => {==}
                    case False{}:
                      h => {==}

def up.imp(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, -y: Word(27n), ey: {y == up.two() : Word(27n)}) -> {Char.is_upper(up.C(b0, b1, b2, b3, b4, y)) == True{} : Bool} -> up.G(up.C(b0, b1, b2, b3, b4, y)):
  %Equal.sym(Word(27n), y, up.two(), ey) : {Char.is_upper(up.C(b0, b1, b2, b3, b4, _)) == True{} : Bool} -> up.G(up.C(b0, b1, b2, b3, b4, _))
  up.bits(b0, b1, b2, b3, b4)

def up.fin(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +y: Word(27n), h0: {Char.is_upper(up.C(b0, b1, b2, b3, b4, y)) == True{} : Bool}, t: Cmp, et: {Word.cmp(27n, y, up.two()) == t : Cmp}, h: {up.U(b0, b1, b2, b3, b4, t) == True{} : Bool}) -> up.G(up.C(b0, b1, b2, b3, b4, y)):
  match t:
    case LT{}:
      absurdF(up.G(up.C(b0, b1, b2, b3, b4, y)), h)
    case GT{}:
      absurdF(up.G(up.C(b0, b1, b2, b3, b4, y)), h)
    case EQ{}:
      up.imp(b0, b1, b2, b3, b4, y, word_eq(27n, y, up.two())(et))(h0)

# an ASCII uppercase letter lowercases to a char other than `_`
def up.lower(+c: Char, +h: {Char.is_upper(c) == True{} : Bool}) -> up.G(c):
  match c:
    case Chr{x}:
      match x:
        case U32{w}:
          match w:
            case WCon{+b0, w1}:
              match w1:
                case WCon{+b1, w2}:
                  match w2:
                    case WCon{+b2, w3}:
                      match w3:
                        case WCon{+b3, w4}:
                          match w4:
                            case WCon{+b4, +y}:
                              up.fin(b0, b1, b2, b3, b4, y, h, Word.cmp(27n, y, up.two()), {==}, h)

def u32_eq(+a: U32, +b: U32, et: {U32.cmp(a, b) == EQ{} : Cmp}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, word_eq(32n, x, y)(et))

def sound_fin(+a: U32, +b: U32, t: Cmp, et: {U32.cmp(a, b) == t : Cmp}, e: {Cmp.is_eq(t) == True{} : Bool}) -> {a == b : U32}:
  match t:
    case LT{}:
      absurdF({a == b : U32}, e)
    case EQ{}:
      u32_eq(a, b, et)
    case GT{}:
      absurdF({a == b : U32}, e)

def char_sound(+c: Char, +d: Char, e: {Char.is_eq(c, d) == True{} : Bool}) -> {c == d : Char}:
  match c d:
    case Chr{+x} Chr{+y}:
      Equal.cong(U32, Char, u => Chr{u}, x, y, sound_fin(x, y, U32.cmp(x, y), {==}, e))
