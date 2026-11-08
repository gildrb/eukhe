# eukhe: lemmas the proofs of area arg_repair share: logic, and String.eq
# is equality (copied from proof/autoresearch/base/step.bend, prefix ab.)

import Base

# Logic
# -----

def ab.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# False is not True: anything follows
def ab.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ab.BD(_, A, Unit)
  Unit{}

def ab.absurd_tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : ab.BD(_, Unit, A)
  Unit{}

def ab.MB(m: Maybe<&2, String>, g: Type) -> Type:
  match m:
    case None{}:
      g
    case Some{t}:
      Unit

# a text is no nothing
def ab.some_none(-A: Type, -t: String, e: {Some{t} == None{} : Maybe<&2, String>}) -> A:
  %e : ab.MB(_, A)
  Unit{}

def ab.fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def ab.snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

def ab.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ab.absurd({False{} == True{} : Bool}, e)

def ab.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      ab.absurd({b == True{} : Bool}, e)

# a or b, with b raised to c
def ab.or_mono(a: Bool, -b: Bool, -c: Bool, f: {b == True{} : Bool} -> {c == True{} : Bool}, e: {Bool.or(a, b) == True{} : Bool}) -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(e)

def ab.or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# Numbers
# -------

def ab.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %ab.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def ab.zero_add(+n: Nat) -> {n == Nat.add(n, 0n) : Nat}:
  Equal.sym(Nat, Nat.add(n, 0n), n, ab.add_zero(n))

def ab.add_one(n: Nat) -> {Nat.add(n, 1n) == 1n+n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %ab.add_one(p) : {1n+Nat.add(p, 1n) == 1n+_ : Nat}
      {==}

def ab.nat_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ab.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      ab.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %ab.nat_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# Strings
# -------

def ab.lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  ab.absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e))

def ab.gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  ab.absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), GT{}, EQ{}, e))

def ab.cmp_eq_fin(-p: Nat, -at: Word(p), -bt: Word(p), t: Cmp, +ab: Bool, +bb: Bool,
  et: {Word.cmp(p, at, bt) == t : Cmp},
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match t:
    case LT{}:
      ab.lt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case GT{}:
      ab.gt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt, rec(et))
        case False{} True{}:
          ab.lt_eq({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, e)
        case True{} False{}:
          ab.gt_eq({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, e)
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt, rec(et))

def ab.word_eq(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e => ab.cmp_eq_fin(p, at, bt, Word.cmp(p, at, bt), ab, bb, {==}, ab.word_eq(p, at, bt), e)

def ab.u32_eq(+a: U32, +b: U32) -> {U32.cmp(a, b) == EQ{} : Cmp} -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      e => Equal.cong(Word(32n), U32, w => U32{w}, x, y, ab.word_eq(32n, x, y)(e))

def ab.word_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case True{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, ab.word_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}
            case False{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, ab.word_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}

def ab.u32_refl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      ab.word_refl(32n, w)

def ab.str_cons(+x: U32, +y: U32, +t1: String, -t2: String, r: {t1 == t2 : String} & {U32.cmp(x, y) == EQ{} : Cmp}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {EQ{} == EQ{} : Cmp}:
  (p, q) = r
  %p : {SCon{Chr{x}, t1} == SCon{Chr{y}, _} : String} & {EQ{} == EQ{} : Cmp}
  %ab.u32_eq(x, y)(q) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t1} : String} & {EQ{} == EQ{} : Cmp}
  ({==}, {==})

# two strings the order calls equal (from EQ so far) are equal
def ab.str_sound(+a: String, +b: String, c: Cmp, e: {Cmp.is_eq(String.order.go(a, b, c)) == True{} : Bool}) -> {a == b : String} & {c == EQ{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      match c:
        case LT{}:
          ab.absurd({SNil{} == SNil{} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          ({==}, {==})
        case GT{}:
          ab.absurd({SNil{} == SNil{} : String} & {GT{} == EQ{} : Cmp}, e)
    case SNil{} SCon{h, t}:
      match c:
        case LT{}:
          ab.absurd({SNil{} == SCon{h, t} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          ab.absurd({SNil{} == SCon{h, t} : String} & {EQ{} == EQ{} : Cmp}, e)
        case GT{}:
          ab.absurd({SNil{} == SCon{h, t} : String} & {GT{} == EQ{} : Cmp}, e)
    case SCon{h, t} SNil{}:
      match c:
        case LT{}:
          ab.absurd({SCon{h, t} == SNil{} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          ab.absurd({SCon{h, t} == SNil{} : String} & {EQ{} == EQ{} : Cmp}, e)
        case GT{}:
          ab.absurd({SCon{h, t} == SNil{} : String} & {GT{} == EQ{} : Cmp}, e)
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          ab.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          ab.str_cons(x, y, t1, t2, ab.str_sound(t1, t2, U32.cmp(x, y), e))
        case GT{}:
          ab.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {GT{} == EQ{} : Cmp}, e)

# String.eq is equality
def ab.str_eq(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  ab.fst({a == b : String}, {EQ{} == EQ{} : Cmp}, ab.str_sound(a, b, EQ{}, e))

def ab.str_order_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{} : Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, ab.u32_refl(x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
          ab.str_order_refl(t)

def ab.str_refl(a: String) -> {String.eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, String.order.go(a, a, EQ{}), EQ{}, ab.str_order_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

