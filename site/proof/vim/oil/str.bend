# eukhe.com's Neovim: string facts for the Oil laws
# =================================================

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../laws/vim/base.bend as Laws
import ../../base.bend as L

# Equal strings
# -------------

def Cmp.If(c: Cmp, G: Type) -> Type:
  match c:
    case EQ{}:
      Unit
    case LT{}:
      G
    case GT{}:
      G

# LT and GT are not EQ: anything follows
def Cmp.lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  %Equal.sym(Cmp, LT{}, EQ{}, e) : Cmp.If(_, G)
  Unit{}

def Cmp.gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  %Equal.sym(Cmp, GT{}, EQ{}, e) : Cmp.If(_, G)
  Unit{}

# two bits that compare EQ are equal
def Bool.cmp_eq(a: Bool, b: Bool, h: {Bool.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Cmp.lt_eq({False{} == True{} : Bool}, h)
    case True{} False{}:
      Cmp.gt_eq({True{} == False{} : Bool}, h)
    case True{} True{}:
      {==}

# a word comparison's last step is EQ only after an EQ, on equal bits
def Fin.c(-ab: Bool, -bb: Bool, c: Cmp, h: {Word.cmp.fin(ab, bb, c) == EQ{} : Cmp}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Cmp.lt_eq({LT{} == EQ{} : Cmp}, h)
    case EQ{}:
      {==}
    case GT{}:
      Cmp.gt_eq({GT{} == EQ{} : Cmp}, h)

def Fin.b(ab: Bool, bb: Bool, c: Cmp, h: {Word.cmp.fin(ab, bb, c) == EQ{} : Cmp}) -> {ab == bb : Bool}:
  match c:
    case LT{}:
      Cmp.lt_eq({ab == bb : Bool}, h)
    case EQ{}:
      Bool.cmp_eq(ab, bb, h)
    case GT{}:
      Cmp.gt_eq({ab == bb : Bool}, h)

def Word.eq_true(+n: Nat, a: Word(n), b: Word(n), +h: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %Word.eq_true(p, at, bt, Fin.c(ab, bb, Word.cmp(p, at, bt), h)) : {WCon{ab, at} == WCon{bb, _} : Word(1n+p)}
          %Fin.b(ab, bb, Word.cmp(p, at, bt), h) : {WCon{ab, at} == WCon{_, at} : Word(1n+p)}
          {==}

def Cmp.is_eq_true(c: Cmp, h: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      L.Bool.false_true({LT{} == EQ{} : Cmp}, h)
    case EQ{}:
      {==}
    case GT{}:
      L.Bool.false_true({GT{} == EQ{} : Cmp}, h)

def U32.eq_true(a: U32, b: U32, h: {U32.cmp(a, b) == EQ{} : Cmp}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %Word.eq_true(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

def Char.eq_true(a: Char, b: Char, h: {Char.is_eq(a, b) == True{} : Bool}) -> {a == b : Char}:
  match a b:
    case Chr{+x} Chr{+y}:
      %U32.eq_true(x, y, Cmp.is_eq_true(U32.cmp(x, y), h)) : {Chr{x} == Chr{_} : Char}
      {==}

# a comparison of strings started from c ends EQ only when c is EQ
def Order.c(a: String, b: String, c: Cmp, h: {String.order.go(a, b, c) == EQ{} : Cmp}) -> {c == EQ{} : Cmp}:
  match a b c:
    case SNil{} SNil{} LT{}:
      h
    case SNil{} SNil{} EQ{}:
      {==}
    case SNil{} SNil{} GT{}:
      h
    case SNil{} SCon{Chr{y}, t2} LT{}:
      h
    case SNil{} SCon{Chr{y}, t2} EQ{}:
      {==}
    case SNil{} SCon{Chr{y}, t2} GT{}:
      h
    case SCon{Chr{x}, t1} SNil{} LT{}:
      h
    case SCon{Chr{x}, t1} SNil{} EQ{}:
      {==}
    case SCon{Chr{x}, t1} SNil{} GT{}:
      h
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} LT{}:
      h
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} EQ{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} GT{}:
      h

def Order.eq(a: String, b: String, +h: {String.order.go(a, b, EQ{}) == EQ{} : Cmp}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, t2}:
      Cmp.lt_eq({SNil{} == SCon{y, t2} : String}, h)
    case SCon{x, t1} SNil{}:
      Cmp.gt_eq({SCon{x, t1} == SNil{} : String}, h)
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      +hc = Order.c(t1, t2, U32.cmp(x, y), h)
      +ht = Equal.trans(Cmp, String.order.go(t1, t2, EQ{}), String.order.go(t1, t2, U32.cmp(x, y)), EQ{}, Equal.cong(Cmp, Cmp, c => String.order.go(t1, t2, c), EQ{}, U32.cmp(x, y), Equal.sym(Cmp, U32.cmp(x, y), EQ{}, hc)), h)
      %Order.eq(t1, t2, ht) : {SCon{Chr{x}, t1} == SCon{Chr{y}, _} : String}
      %U32.eq_true(x, y, hc) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t1} : String}
      {==}

# String.eq says equal only of equal strings
def Str.eq_true(+a: String, +b: String, h: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  Order.eq(a, b, Cmp.is_eq_true(String.order.go(a, b, EQ{}), h))
