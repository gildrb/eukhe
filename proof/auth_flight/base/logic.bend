# eukhe: lemmas of the desk's safety proofs that call nothing of the
# desk: Bool, Nat and String facts (String.eq is equality).

import Base
import ../../../bend/auth_flight.bend as F
import ../../../laws/auth_flight/entry.bend as S
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../../laws/auth_flight/safety.bend as SS
import ./entry.bend as LAE

# Logic
# -----

def ad.and_l(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ad.and_r(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LAE.ae.ft({b == True{} : Bool}, h)

def ad.and_tt(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def ad.or_l(+a: Bool, +b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, h) : {Bool.or(_, b) == True{} : Bool}
  {==}

def ad.or_r(+a: Bool, +b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# a Bool and its value
def ad.which(b: Bool) -> (&v: Bool -> {b == v : Bool}):
  match b:
    case True{}:
      (True{}, {==})
    case False{}:
      (False{}, {==})

# Nat
# ---

def ad.eq_true(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LAE.ae.ft({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LAE.ae.ft({1n+p == 0n : Nat}, h)
    case 1n++p 1n++q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, ad.eq_true(p, q, h))

def ad.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ad.eq_refl(p)

def ad.lt_succ(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      LAE.ae.ft({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ad.lt_succ(p, q, h)

def ad.lt_self(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ad.lt_self(p)

# a number below b is not b
def ad.lt_ne(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LAE.ae.ft({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ad.lt_ne(p, q, h)

def ad.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ad.le_refl(p)

def ad.le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n _:
      LAE.ae.ft({Nat.is_le(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      LAE.ae.ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      ad.le_trans(p, q, r, h1, h2)

def ad.le_succ_r(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ad.le_succ_r(p)

# x + a <= x + b when a <= b

# a <= x + a
def ad.le_add_l(x: Nat, +a: Nat) -> {Nat.is_le(a, Nat.add(x, a)) == True{} : Bool}:
  match x:
    case 0n:
      ad.le_refl(a)
    case 1n++p:
      ad.le_trans(a, Nat.add(p, a), 1n+Nat.add(p, a), ad.le_add_l(p, a), ad.le_succ_r(Nat.add(p, a)))

def ad.le_add_mono(x: Nat, a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, a), Nat.add(x, b)) == True{} : Bool}:
  match x:
    case 0n:
      h
    case 1n+p:
      ad.le_add_mono(p, a, b, h)

# b + (1 + c) == 1 + (b + c)
def ad.add_succ(b: Nat, +c: Nat) -> {1n+Nat.add(b, c) == Nat.add(b, 1n+c) : Nat}:
  match b:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, x => 1n+x, 1n+Nat.add(p, c), Nat.add(p, 1n+c), ad.add_succ(p, c))

# Strings
# -------


# a + (b + c) == b + (a + c)
def ad.add_swap(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(p, Nat.add(b, c)), Nat.add(b, Nat.add(p, c)), ad.add_swap(p, b, c)) : {1n+_ == Nat.add(b, 1n+Nat.add(p, c)) : Nat}
      ad.add_succ(b, Nat.add(p, c))

def ad.go_lt(a: String, b: String) -> {String.order.go(a, b, LT{}) == LT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def ad.go_gt(a: String, b: String) -> {String.order.go(a, b, GT{}) == GT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def ad.cmp_fin(+x: U32, +y: U32, t1: String, t2: String, c: Cmp, ec: {U32.cmp(x, y) == c : Cmp},
  rec: {String.order.go(t1, t2, EQ{}) == EQ{} : Cmp} -> {t1 == t2 : String},
  e: {String.order.go(t1, t2, c) == EQ{} : Cmp}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}:
  match c:
    case LT{}:
      LAE.ae.ft({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), LT{}, EQ{}, Equal.trans(Cmp, LT{}, String.order.go(t1, t2, LT{}), EQ{}, Equal.sym(Cmp, String.order.go(t1, t2, LT{}), LT{}, ad.go_lt(t1, t2)), e)))
    case EQ{}:
      +ex = PWireBoolExact.wr_cmp_eq(x, y)(ec)
      +et = rec(e)
      %ex : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %et : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}
    case GT{}:
      LAE.ae.ft({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), GT{}, EQ{}, Equal.trans(Cmp, GT{}, String.order.go(t1, t2, GT{}), EQ{}, Equal.sym(Cmp, String.order.go(t1, t2, GT{}), GT{}, ad.go_gt(t1, t2)), e)))

def ad.str_go_eq(+a: String, +b: String) -> {String.order.go(a, b, EQ{}) == EQ{} : Cmp} -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      e => {==}
    case SNil{} SCon{h, t}:
      e => LAE.ae.ft({SNil{} == SCon{h, t} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), LT{}, EQ{}, e))
    case SCon{h, t} SNil{}:
      e => LAE.ae.ft({SCon{h, t} == SNil{} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), GT{}, EQ{}, e))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      e => ad.cmp_fin(x, y, t1, t2, U32.cmp(x, y), {==}, ad.str_go_eq(t1, t2), e)

def ad.str_fin(+a: String, +b: String, c: Cmp, ec: {String.order(a, b) == c : Cmp}, e: {Cmp.is_eq(c) == True{} : Bool}) -> {a == b : String}:
  match c:
    case LT{}:
      LAE.ae.ft({a == b : String}, e)
    case EQ{}:
      ad.str_go_eq(a, b)(ec)
    case GT{}:
      LAE.ae.ft({a == b : String}, e)

# String.eq is equality
def ad.str_sound(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  ad.str_fin(a, b, String.order(a, b), {==}, e)

def ad.bool_cmp_refl(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ad.word_cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, ad.word_cmp_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          ad.bool_cmp_refl(b)

def ad.u32_refl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      ad.word_cmp_refl(32n, w)

def ad.str_go_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{} : Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, t}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, ad.u32_refl(x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
      ad.str_go_refl(t)

def ad.str_refl(a: String) -> {String.eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, String.order.go(a, a, EQ{}), EQ{}, ad.str_go_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def ad.str_sym_fin(+a: String, +b: String, v: Bool, +ev: {String.eq(a, b) == v : Bool}, h: {String.eq(b, a) == False{} : Bool}) -> {String.eq(a, b) == False{} : Bool}:
  match v:
    case True{}:
      +eab = ad.str_sound(a, b, ev)
      +x = Equal.trans(Bool, String.eq(b, b), String.eq(b, a), False{}, Equal.cong(String, Bool, s => String.eq(b, s), b, a, Equal.sym(String, a, b, eab)), h)
      LAE.ae.tf({String.eq(a, b) == False{} : Bool}, Equal.trans(Bool, True{}, String.eq(b, b), False{}, Equal.sym(Bool, String.eq(b, b), True{}, ad.str_refl(b)), x))
    case False{}:
      ev

# String.eq differs both ways
def ad.str_ne_sym(+a: String, +b: String, h: {String.eq(b, a) == False{} : Bool}) -> {String.eq(a, b) == False{} : Bool}:
  ad.str_sym_fin(a, b, String.eq(a, b), {==}, h)
