# eukhe: logic lemmas of the proofs of area glob: Bool algebra, U32 order
# (a <= b and b <= a is a == b, through Word.cmp turned around), lists

import Base

# Bool
# ----

def gl.BF(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

# False is not True: anything follows
def gl.ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : gl.BF(_, A)
  Unit{}

def gl.BT(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      A

# True is not False: anything follows
def gl.tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : gl.BT(_, A)
  Unit{}

def gl.or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gl.or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gl.or_idem(b: Bool) -> {Bool.or(b, b) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gl.and_true(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gl.and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gl.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      gl.ft({False{} == True{} : Bool}, e)

def gl.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      gl.ft({b == True{} : Bool}, e)

def gl.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      gl.ft({Bool.and(False{}, b) == True{} : Bool}, ea)

def gl.or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      gl.ft({Bool.or(False{}, b) == True{} : Bool}, e)

def gl.or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def gl.or_ff(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      gl.tf({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def gl.or_fr(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      gl.tf({b == False{} : Bool}, e)
    case False{}:
      e

def gl.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def gl.or_comm(a: Bool, b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def gl.and_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a and (b or c) is (a and b) or (a and c)
def gl.and_or(a: Bool, +b: Bool, +c: Bool) -> {Bool.and(a, Bool.or(b, c)) == Bool.or(Bool.and(a, b), Bool.and(a, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# (a or b) and c is (a and c) or (b and c)
def gl.or_and(a: Bool, b: Bool, c: Bool) -> {Bool.and(Bool.or(a, b), c) == Bool.or(Bool.and(a, c), Bool.and(b, c)) : Bool}:
  match a b c:
    case True{} b True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} b c:
      {==}

# (a or b) or (c or d) is (a or c) or (b or d)
def gl.or_swap(a: Bool, b: Bool, c: Bool, d: Bool) -> {Bool.or(Bool.or(a, b), Bool.or(c, d)) == Bool.or(Bool.or(a, c), Bool.or(b, d)) : Bool}:
  match a b c d:
    case True{} b c d:
      {==}
    case False{} True{} True{} d:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} c d:
      {==}

# equal parts, equal and
def gl.and_c(-a: Bool, -b: Bool, -c: Bool, -d: Bool, ab: {a == b : Bool}, cd: {c == d : Bool}) -> {Bool.and(a, c) == Bool.and(b, d) : Bool}:
  %ab : {Bool.and(a, c) == Bool.and(_, d) : Bool}
  %cd : {Bool.and(a, c) == Bool.and(a, _) : Bool}
  {==}

# equal parts, equal pair
def gl.pair(-a: Bool, -b: Bool, -c: Bool, -d: Bool, ac: {a == c : Bool}, bd: {b == d : Bool}) -> {(a, b) == (c, d) : Bool & Bool}:
  %ac : {(a, b) == (_, d) : Bool & Bool}
  %bd : {(a, b) == (a, _) : Bool & Bool}
  {==}

# U32 order
# ---------

def gl.cflip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def gl.fin_flip(t: Cmp, ab: Bool, bb: Bool) -> {Word.cmp.fin(bb, ab, gl.cflip(t)) == gl.cflip(Word.cmp.fin(ab, bb, t)) : Cmp}:
  match t:
    case LT{}:
      {==}
    case EQ{}:
      match ab bb:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}
    case GT{}:
      {==}

# comparing b with a is comparing a with b, turned around
def gl.w_flip(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, b, a) == gl.cflip(Word.cmp(n, a, b)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, bt, at), gl.cflip(Word.cmp(p, at, bt)), gl.w_flip(p, at, bt)) : {Word.cmp.fin(bb, ab, _) == gl.cflip(Word.cmp.fin(ab, bb, Word.cmp(p, at, bt))) : Cmp}
          gl.fin_flip(Word.cmp(p, at, bt), ab, bb)

def gl.le_le_c(c: Cmp) -> {Bool.and(Cmp.is_le(c), Cmp.is_le(gl.cflip(c))) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def gl.eq_c(c: Cmp) -> {Cmp.is_eq(gl.cflip(c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a <= b and b <= a: a is b
def gl.le_le(a: U32, b: U32) -> {Bool.and(U32.is_le(a, b), U32.is_le(b, a)) == U32.is_eq(a, b) : Bool}:
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Cmp, Word.cmp(32n, y, x), gl.cflip(Word.cmp(32n, x, y)), gl.w_flip(32n, x, y)) : {Bool.and(Cmp.is_le(Word.cmp(32n, x, y)), Cmp.is_le(_)) == Cmp.is_eq(Word.cmp(32n, x, y)) : Bool}
      gl.le_le_c(Word.cmp(32n, x, y))

def gl.eq_sym(a: U32, b: U32) -> {U32.is_eq(b, a) == U32.is_eq(a, b) : Bool}:
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Cmp, Word.cmp(32n, y, x), gl.cflip(Word.cmp(32n, x, y)), gl.w_flip(32n, x, y)) : {Cmp.is_eq(_) == Cmp.is_eq(Word.cmp(32n, x, y)) : Bool}
      gl.eq_c(Word.cmp(32n, x, y))

# x within b..b is x == b
def gl.in_one(+b: U32, +x: U32) -> {Bool.or(Bool.and(U32.is_le(b, x), U32.is_le(x, b)), False{}) == U32.is_eq(x, b) : Bool}:
  %Equal.sym(Bool, Bool.or(Bool.and(U32.is_le(b, x), U32.is_le(x, b)), False{}), Bool.and(U32.is_le(b, x), U32.is_le(x, b)), gl.or_false(Bool.and(U32.is_le(b, x), U32.is_le(x, b)))) : {_ == U32.is_eq(x, b) : Bool}
  %Equal.sym(Bool, U32.is_eq(x, b), U32.is_eq(b, x), gl.eq_sym(b, x)) : {Bool.and(U32.is_le(b, x), U32.is_le(x, b)) == _ : Bool}
  gl.le_le(b, x)

# Lists
# -----

def gl.app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      Equal.cong(List<&2, A>, List<&2, A>, z => x <> z, List.append(&2, A, t, Nil{}), t, gl.app_nil(A, t))

def gl.app_assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      Equal.cong(List<&2, A>, List<&2, A>, z => x <> z, List.append(&2, A, List.append(&2, A, t, ys), zs), List.append(&2, A, t, List.append(&2, A, ys, zs)), gl.app_assoc(A, t, ys, zs))
