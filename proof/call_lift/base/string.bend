# eukhe: String lemmas of area call_lift
#
# String.eq is reflexive (clm.str_refl), through the order of a string
# with itself (clm.str_order_refl) and of a U32 / Word with itself.

import Base

def clm.word_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
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
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, clm.word_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}
            case False{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, clm.word_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}

def clm.u32_refl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      clm.word_refl(32n, w)

def clm.str_order_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{} : Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, clm.u32_refl(x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
          clm.str_order_refl(t)

# String.eq(a, a) holds
def clm.str_refl(a: String) -> {String.eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, String.order.go(a, a, EQ{}), EQ{}, clm.str_order_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# True is String.eq(a, a), the side the rewrites read
def clm.str_refl_sym(+a: String) -> {True{} == String.eq(a, a) : Bool}:
  Equal.sym(Bool, String.eq(a, a), True{}, clm.str_refl(a))
