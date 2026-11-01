# eukhe: lemmas of the cron_serve proofs that call nothing of the serve:
# Bool, Nat and String facts (String.eq is equality).

import Base
import ../../wire/wire_bool_exact.bend as PWireBoolExact

# Logic
# -----

def lg.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a claim that True is False proves anything
def lg.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : lg.If(_, G)
  Unit{}

def lg.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  lg.tf(G, Equal.sym(Bool, False{}, True{}, e))

# a Bool and its value
def lg.which(b: Bool) -> (&v: Bool -> {b == v : Bool}):
  match b:
    case True{}:
      (True{}, {==})
    case False{}:
      (False{}, {==})

def lg.and_l(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      lg.ft({False{} == True{} : Bool}, h)

def lg.and_r(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      lg.ft({b == True{} : Bool}, h)

def lg.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Nat
# ---

def lg.eq_true(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      lg.ft({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      lg.ft({1n+p == 0n : Nat}, h)
    case 1n++p 1n++q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, lg.eq_true(p, q, h))

def lg.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lg.eq_refl(p)

# Strings
# -------

def lg.go_lt(a: String, b: String) -> {String.order.go(a, b, LT{}) == LT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def lg.go_gt(a: String, b: String) -> {String.order.go(a, b, GT{}) == GT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def lg.cmp_fin(+x: U32, +y: U32, t1: String, t2: String, c: Cmp, ec: {U32.cmp(x, y) == c : Cmp},
  rec: {String.order.go(t1, t2, EQ{}) == EQ{} : Cmp} -> {t1 == t2 : String},
  e: {String.order.go(t1, t2, c) == EQ{} : Cmp}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}:
  match c:
    case LT{}:
      lg.ft({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), LT{}, EQ{}, Equal.trans(Cmp, LT{}, String.order.go(t1, t2, LT{}), EQ{}, Equal.sym(Cmp, String.order.go(t1, t2, LT{}), LT{}, lg.go_lt(t1, t2)), e)))
    case EQ{}:
      +ex = PWireBoolExact.wr_cmp_eq(x, y)(ec)
      +et = rec(e)
      %ex : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %et : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}
    case GT{}:
      lg.ft({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), GT{}, EQ{}, Equal.trans(Cmp, GT{}, String.order.go(t1, t2, GT{}), EQ{}, Equal.sym(Cmp, String.order.go(t1, t2, GT{}), GT{}, lg.go_gt(t1, t2)), e)))

def lg.str_go_eq(+a: String, +b: String) -> {String.order.go(a, b, EQ{}) == EQ{} : Cmp} -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      e => {==}
    case SNil{} SCon{h, t}:
      e => lg.ft({SNil{} == SCon{h, t} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), LT{}, EQ{}, e))
    case SCon{h, t} SNil{}:
      e => lg.ft({SCon{h, t} == SNil{} : String}, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), GT{}, EQ{}, e))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      e => lg.cmp_fin(x, y, t1, t2, U32.cmp(x, y), {==}, lg.str_go_eq(t1, t2), e)

def lg.str_fin(+a: String, +b: String, c: Cmp, ec: {String.order(a, b) == c : Cmp}, e: {Cmp.is_eq(c) == True{} : Bool}) -> {a == b : String}:
  match c:
    case LT{}:
      lg.ft({a == b : String}, e)
    case EQ{}:
      lg.str_go_eq(a, b)(ec)
    case GT{}:
      lg.ft({a == b : String}, e)

# String.eq is equality
def lg.str_sound(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  lg.str_fin(a, b, String.order(a, b), {==}, e)

def lg.bool_cmp_refl(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def lg.word_cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, lg.word_cmp_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          lg.bool_cmp_refl(b)

def lg.u32_refl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      lg.word_cmp_refl(32n, w)

def lg.str_go_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{} : Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, t}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, lg.u32_refl(x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
      lg.str_go_refl(t)

def lg.str_refl(a: String) -> {String.eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, String.order.go(a, a, EQ{}), EQ{}, lg.str_go_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}
