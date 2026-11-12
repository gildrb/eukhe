# eukhe: the order of 32-bit words, for the laws of area color that compare
# two U32 (light, near, dist): the order one way is the flip of the order
# the other way (cw.anti), the order of a against c follows from a against
# b and b against c wherever those two decide it (cw.trans), no word is
# above the word of all ones (cw.top). Then the facts on U32.is_le,
# U32.is_lt, U32.is_gt and U32.is_ge the proofs read. Every lemma walks
# the bits; none reads a word as a natural.

import Base

def cw.T(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True
def cw.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : cw.T(_, G)
  Unit{}

def cw.F(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def cw.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : cw.F(_, G)
  Unit{}

# The flip
# --------

def cw.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def cw.fin_flip(c: Cmp, a: Bool, b: Bool) -> {Word.cmp.fin(a, b, cw.flip(c)) == cw.flip(Word.cmp.fin(b, a, c)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match a b:
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

# a word's order is the flip of the order the other way
def cw.wanti(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == cw.flip(Word.cmp(n, b, a)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), cw.flip(Word.cmp(p, bt, at)), cw.wanti(p, at, bt)) : {Word.cmp.fin(ab, bb, _) == cw.flip(Word.cmp.fin(bb, ab, Word.cmp(p, bt, at))) : Cmp}
          cw.fin_flip(Word.cmp(p, bt, at), ab, bb)

def cw.anti(a: U32, b: U32) -> {U32.cmp(a, b) == cw.flip(U32.cmp(b, a)) : Cmp}:
  match a b:
    case U32{x} U32{y}:
      cw.wanti(32n, x, y)

# Three words
# -----------

# what a against b (x) and b against c (y) say of a against c (z): below
# then below or equal is below, above then above or equal is above, equal
# then anything is that; below then above, above then below say nothing
def cw.Tr(x: Cmp, y: Cmp, z: Cmp) -> Type:
  match x:
    case LT{}:
      match y:
        case LT{}:
          {z == LT{} : Cmp}
        case EQ{}:
          {z == LT{} : Cmp}
        case GT{}:
          Unit
    case EQ{}:
      {z == y : Cmp}
    case GT{}:
      match y:
        case LT{}:
          Unit
        case EQ{}:
          {z == GT{} : Cmp}
        case GT{}:
          {z == GT{} : Cmp}

def cw.step.lt(b: Bool, c: Bool) -> cw.Tr(LT{}, Bool.cmp(b, c), LT{}):
  match b c:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      Unit{}
    case True{} True{}:
      {==}

def cw.step.gt(b: Bool, c: Bool) -> cw.Tr(GT{}, Bool.cmp(b, c), GT{}):
  match b c:
    case False{} False{}:
      {==}
    case False{} True{}:
      Unit{}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def cw.step.eq_lt(a: Bool, b: Bool) -> cw.Tr(Bool.cmp(a, b), LT{}, LT{}):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      Unit{}
    case True{} True{}:
      {==}

def cw.step.eq_gt(a: Bool, b: Bool) -> cw.Tr(Bool.cmp(a, b), GT{}, GT{}):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Unit{}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def cw.step.bits(a: Bool, b: Bool, c: Bool) -> cw.Tr(Bool.cmp(a, b), Bool.cmp(b, c), Bool.cmp(a, c)):
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      Unit{}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      Unit{}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# one more bit below the bits compared so far
def cw.step(a: Bool, b: Bool, c: Bool, x: Cmp, y: Cmp, z: Cmp, ih: cw.Tr(x, y, z)) -> cw.Tr(Word.cmp.fin(a, b, x), Word.cmp.fin(b, c, y), Word.cmp.fin(a, c, z)):
  match x:
    case LT{}:
      match y:
        case LT{}:
          %Equal.sym(Cmp, z, LT{}, ih) : {Word.cmp.fin(a, c, _) == LT{} : Cmp}
          {==}
        case EQ{}:
          %Equal.sym(Cmp, z, LT{}, ih) : cw.Tr(LT{}, Bool.cmp(b, c), Word.cmp.fin(a, c, _))
          cw.step.lt(b, c)
        case GT{}:
          Unit{}
    case EQ{}:
      match y:
        case LT{}:
          %Equal.sym(Cmp, z, LT{}, ih) : cw.Tr(Bool.cmp(a, b), LT{}, Word.cmp.fin(a, c, _))
          cw.step.eq_lt(a, b)
        case EQ{}:
          %Equal.sym(Cmp, z, EQ{}, ih) : cw.Tr(Bool.cmp(a, b), Bool.cmp(b, c), Word.cmp.fin(a, c, _))
          cw.step.bits(a, b, c)
        case GT{}:
          %Equal.sym(Cmp, z, GT{}, ih) : cw.Tr(Bool.cmp(a, b), GT{}, Word.cmp.fin(a, c, _))
          cw.step.eq_gt(a, b)
    case GT{}:
      match y:
        case LT{}:
          Unit{}
        case EQ{}:
          %Equal.sym(Cmp, z, GT{}, ih) : cw.Tr(GT{}, Bool.cmp(b, c), Word.cmp.fin(a, c, _))
          cw.step.gt(b, c)
        case GT{}:
          %Equal.sym(Cmp, z, GT{}, ih) : {Word.cmp.fin(a, c, _) == GT{} : Cmp}
          {==}

def cw.wtrans(n: Nat, a: Word(n), b: Word(n), c: Word(n)) -> cw.Tr(Word.cmp(n, a, b), Word.cmp(n, b, c), Word.cmp(n, a, c)):
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a b c:
        case WCon{a0, +at} WCon{+b0, +bt} WCon{c0, +ct}:
          cw.step(a0, b0, c0, Word.cmp(p, at, bt), Word.cmp(p, bt, ct), Word.cmp(p, at, ct), cw.wtrans(p, at, bt, ct))

# the order of a against c, from a against b and b against c
def cw.trans(a: U32, b: U32, c: U32) -> cw.Tr(U32.cmp(a, b), U32.cmp(b, c), U32.cmp(a, c)):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      cw.wtrans(32n, x, y, z)

# the same, with the first order given as p
def cw.cast(-u: Cmp, -p: Cmp, -q: Cmp, -r: Cmp, e: {u == p : Cmp}, t: cw.Tr(u, q, r)) -> cw.Tr(p, q, r):
  %e : cw.Tr(_, q, r)
  t

# The top word
# ------------

def cw.ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, cw.ones(p)}

def cw.top.fin(t: Cmp, b0: Bool, h: {Cmp.is_le(t) == True{} : Bool}) -> {Cmp.is_le(Word.cmp.fin(b0, True{}, t)) == True{} : Bool}:
  match t:
    case LT{}:
      {==}
    case EQ{}:
      match b0:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      h

def cw.wtop(n: Nat, w: Word(n)) -> {Cmp.is_le(Word.cmp(n, w, cw.ones(n))) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w:
        case WCon{b0, +t}:
          cw.top.fin(Word.cmp(p, t, cw.ones(p)), b0, cw.wtop(p, t))

# every U32 is at most 4294967295
def cw.top(a: U32) -> {U32.is_le(a, 4294967295) == True{} : Bool}:
  match a:
    case U32{w}:
      cw.wtop(32n, w)

# The facts the proofs read
# -------------------------

def cw.le_gt.go(p: Cmp, q: Cmp, r: Cmp, t: cw.Tr(cw.flip(p), q, r), h1: {Cmp.is_le(q) == True{} : Bool}, h2: {Cmp.is_gt(p) == True{} : Bool}) -> {Cmp.is_gt(cw.flip(r)) == True{} : Bool}:
  match p:
    case LT{}:
      cw.ft({Cmp.is_gt(cw.flip(r)) == True{} : Bool}, h2)
    case EQ{}:
      cw.ft({Cmp.is_gt(cw.flip(r)) == True{} : Bool}, h2)
    case GT{}:
      match q:
        case LT{}:
          %Equal.sym(Cmp, r, LT{}, t) : {Cmp.is_gt(cw.flip(_)) == True{} : Bool}
          {==}
        case EQ{}:
          %Equal.sym(Cmp, r, LT{}, t) : {Cmp.is_gt(cw.flip(_)) == True{} : Bool}
          {==}
        case GT{}:
          cw.ft({Cmp.is_gt(cw.flip(r)) == True{} : Bool}, h1)

# x <= y and x > k give y > k
def cw.le_gt(+x: U32, +y: U32, +k: U32, h1: {U32.is_le(x, y) == True{} : Bool}, h2: {U32.is_gt(x, k) == True{} : Bool}) -> {U32.is_gt(y, k) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(y, k), cw.flip(U32.cmp(k, y)), cw.anti(y, k)) : {Cmp.is_gt(_) == True{} : Bool}
  cw.le_gt.go(U32.cmp(x, k), U32.cmp(x, y), U32.cmp(k, y), cw.cast(U32.cmp(k, x), cw.flip(U32.cmp(x, k)), U32.cmp(x, y), U32.cmp(k, y), cw.anti(k, x), cw.trans(k, x, y)), h1, h2)

def cw.le_nlt.go(c: Cmp, h: {Cmp.is_le(c) == True{} : Bool}) -> {Cmp.is_lt(cw.flip(c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      cw.ft({Cmp.is_lt(cw.flip(GT{})) == False{} : Bool}, h)

# a <= b gives not b < a
def cw.le_nlt(+a: U32, +b: U32, h: {U32.is_le(a, b) == True{} : Bool}) -> {U32.is_lt(b, a) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(b, a), cw.flip(U32.cmp(a, b)), cw.anti(b, a)) : {Cmp.is_lt(_) == False{} : Bool}
  cw.le_nlt.go(U32.cmp(a, b), h)

def cw.lt_top.go(p: Cmp, q: Cmp, r: Cmp, t: cw.Tr(p, q, r), h: {Cmp.is_lt(p) == True{} : Bool}, hq: {Cmp.is_le(q) == True{} : Bool}) -> {Cmp.is_lt(r) == True{} : Bool}:
  match p:
    case LT{}:
      match q:
        case LT{}:
          %Equal.sym(Cmp, r, LT{}, t) : {Cmp.is_lt(_) == True{} : Bool}
          {==}
        case EQ{}:
          %Equal.sym(Cmp, r, LT{}, t) : {Cmp.is_lt(_) == True{} : Bool}
          {==}
        case GT{}:
          cw.ft({Cmp.is_lt(r) == True{} : Bool}, hq)
    case EQ{}:
      cw.ft({Cmp.is_lt(r) == True{} : Bool}, h)
    case GT{}:
      cw.ft({Cmp.is_lt(r) == True{} : Bool}, h)

# a < b gives a < 4294967295
def cw.lt_top(+a: U32, +b: U32, h: {U32.is_lt(a, b) == True{} : Bool}) -> {U32.is_lt(a, 4294967295) == True{} : Bool}:
  cw.lt_top.go(U32.cmp(a, b), U32.cmp(b, 4294967295), U32.cmp(a, 4294967295), cw.trans(a, b, 4294967295), h, cw.top(b))

def cw.le_ntop.go(q: Cmp, p: Cmp, r: Cmp, t: cw.Tr(p, q, r), h1: {Cmp.is_le(p) == True{} : Bool}, h2: {Cmp.is_lt(r) == False{} : Bool}) -> {Cmp.is_lt(q) == False{} : Bool}:
  match q:
    case LT{}:
      match p:
        case LT{}:
          %t : {Cmp.is_lt(_) == False{} : Bool}
          h2
        case EQ{}:
          %t : {Cmp.is_lt(_) == False{} : Bool}
          h2
        case GT{}:
          cw.ft({Cmp.is_lt(LT{}) == False{} : Bool}, h1)
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a <= b and not a < 4294967295 give not b < 4294967295
def cw.le_ntop(+a: U32, +b: U32, h1: {U32.is_le(a, b) == True{} : Bool}, h2: {U32.is_lt(a, 4294967295) == False{} : Bool}) -> {U32.is_lt(b, 4294967295) == False{} : Bool}:
  cw.le_ntop.go(U32.cmp(b, 4294967295), U32.cmp(a, b), U32.cmp(a, 4294967295), cw.trans(a, b, 4294967295), h1, h2)

# A word against itself
# ---------------------

def cw.brefl(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cw.wrefl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, cw.wrefl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          cw.brefl(b)

# every U32 equals itself
def cw.refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, cw.wrefl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# Logic
# -----

def cw.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def cw.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      cw.ft({b == True{} : Bool}, e)

# a Bool is not both True and False
def cw.clash(-G: Type, b: Bool, h1: {b == True{} : Bool}, h2: {b == False{} : Bool}) -> G:
  match b:
    case True{}:
      cw.tf(G, h2)
    case False{}:
      cw.ft(G, h1)
