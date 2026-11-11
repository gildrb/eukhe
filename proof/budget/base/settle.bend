# eukhe: lemmas of area budget for the proofs about settle and fund
# (bend/budget.bend against spec/budget/ledger.bend): sums of numbers, the
# amount of a sum, of a difference and of zero in one dimension, what the
# code's hold walks (held, owed, others) are in the spec's measures (has,
# held_of, held), and each law over the fields of an account

import Base
import ../../../bend/budget.bend as B
import ../../../spec/budget/ledger.bend as S

# Logic
# -----

def bs.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def bs.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a premise False == True proves anything
def bs.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : bs.IfF(_, G)
  Unit{}

# a premise True == False proves anything
def bs.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : bs.IfT(_, G)
  Unit{}

# Numbers
# -------

def bs.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %bs.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def bs.succ_add(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %bs.succ_add(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def bs.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %bs.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def bs.add_assoc_r(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %bs.add_assoc_r(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

def bs.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, bs.add_zero(b))
    case 1n+p:
      %bs.succ_add(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %bs.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# a + (b + c) = b + (a + c)
def bs.add_lcomm(+a: Nat, +b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  %bs.add_assoc(b, a, c) : {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  %bs.add_comm(a, b) : {Nat.add(a, Nat.add(b, c)) == Nat.add(_, c) : Nat}
  bs.add_assoc_r(a, b, c)

# (a + b) + c = (a + c) + b
def bs.add_rswap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  %bs.add_assoc_r(a, c, b) : {Nat.add(Nat.add(a, b), c) == _ : Nat}
  %bs.add_comm(b, c) : {Nat.add(Nat.add(a, b), c) == Nat.add(a, _) : Nat}
  bs.add_assoc(a, b, c)

# a + (b - a) = (a - b) + b: each is the larger of a and b
def bs.max(a: Nat, b: Nat) -> {Nat.add(a, Nat.sub(b, a)) == Nat.add(Nat.sub(a, b), b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %bs.succ_add(Nat.sub(p, q), q) : {1n+Nat.add(p, Nat.sub(q, p)) == _ : Nat}
      %bs.max(p, q) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

def bs.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      bs.le_refl(p)

# a <= b: a <= b + 1
def bs.le_step(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      bs.absurd_ft({Nat.is_le(p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      bs.le_step(p, q, e)

# a <= w: a <= f + w
def bs.le_add(f: Nat, +a: Nat, +w: Nat, e: {Nat.is_le(a, w) == True{} : Bool}) -> {Nat.is_le(a, Nat.add(f, w)) == True{} : Bool}:
  match f:
    case 0n:
      e
    case 1n++g:
      bs.le_step(a, Nat.add(g, w), bs.le_add(g, a, w, e))

# a <= b: a - b = 0
def bs.sub_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      bs.absurd_ft({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      bs.sub_le(p, q, e)

# a <= w: a - (f + w) = 0
def bs.sub_none(+a: Nat, +f: Nat, +w: Nat, e: {Nat.is_le(a, w) == True{} : Bool}) -> {Nat.sub(a, Nat.add(f, w)) == 0n : Nat}:
  bs.sub_le(a, Nat.add(f, w), bs.le_add(f, a, w, e))

def bs.sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (w + l) - w = l
def bs.sub_add_l(w: Nat, +l: Nat) -> {Nat.sub(Nat.add(w, l), w) == l : Nat}:
  match w:
    case 0n:
      bs.sub_zero(l)
    case 1n+q:
      bs.sub_add_l(q, l)

# (l + w) - w = l
def bs.sub_add_r(+l: Nat, +w: Nat) -> {Nat.sub(Nat.add(l, w), w) == l : Nat}:
  %bs.add_comm(w, l) : {Nat.sub(_, w) == l : Nat}
  bs.sub_add_l(w, l)

# o + (w - (f + w)) = o: a spend of the hold w makes no overrun
def bs.over_full(+o: Nat, +f: Nat, +w: Nat) -> {Nat.add(o, Nat.sub(w, Nat.add(f, w))) == o : Nat}:
  %Equal.sym(Nat, Nat.sub(w, Nat.add(f, w)), 0n, bs.sub_none(w, f, w, bs.le_refl(w))) : {Nat.add(o, _) == o : Nat}
  bs.add_zero(o)

# i is id and j is not: i is not j
def bs.eq_other(i: Nat, j: Nat, id: Nat, e: {Nat.is_eq(i, id) == True{} : Bool}, ne: {Nat.is_eq(j, id) == False{} : Bool}) -> {Nat.is_eq(i, j) == False{} : Bool}:
  match i j id:
    case 0n 0n 0n:
      bs.absurd_tf({True{} == False{} : Bool}, ne)
    case 0n 0n 1n+k:
      bs.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+k:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+k:
      {==}
    case 1n+p 1n+q 0n:
      bs.absurd_ft({Nat.is_eq(p, q) == False{} : Bool}, e)
    case 1n+p 1n+q 1n+k:
      bs.eq_other(p, q, k, e, ne)

# Amounts
# -------

# a sum of amounts is the sum in each dimension (time: no amount)
def bs.at_add4(d: B.Dim, x: B.Amt, y: B.Amt) -> {S.at(d, B.add4(x, y)) == Nat.add(S.at(d, x), S.at(d, y)) : Nat}:
  match d:
    case B.Cost{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Tok{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Time{}:
      {==}
    case B.Calls{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Reqs{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}

# a difference of amounts is the difference in each dimension
def bs.at_sub4(d: B.Dim, x: B.Amt, y: B.Amt) -> {S.at(d, B.sub4(x, y)) == Nat.sub(S.at(d, x), S.at(d, y)) : Nat}:
  match d:
    case B.Cost{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Tok{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Time{}:
      {==}
    case B.Calls{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Reqs{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}

# zero is zero in each dimension
def bs.at_zero(d: B.Dim) -> {S.at(d, B.zero()) == 0n : Nat}:
  match d:
    case B.Cost{}:
      {==}
    case B.Tok{}:
      {==}
    case B.Time{}:
      {==}
    case B.Calls{}:
      {==}
    case B.Reqs{}:
      {==}

def bs.add4_at(d: B.Dim, x: B.Amt, y: B.Amt) -> {Nat.add(S.at(d, x), S.at(d, y)) == S.at(d, B.add4(x, y)) : Nat}:
  Equal.sym(Nat, S.at(d, B.add4(x, y)), Nat.add(S.at(d, x), S.at(d, y)), bs.at_add4(d, x, y))

def bs.sub4_at(d: B.Dim, x: B.Amt, y: B.Amt) -> {Nat.sub(S.at(d, x), S.at(d, y)) == S.at(d, B.sub4(x, y)) : Nat}:
  Equal.sym(Nat, S.at(d, B.sub4(x, y)), Nat.sub(S.at(d, x), S.at(d, y)), bs.at_sub4(d, x, y))

# Holds
# -----

def bs.held_is(same: Bool, -x: Bool, -y: Bool, e: {x == y : Bool}) -> {B.held.is(same, x) == Bool.or(same, y) : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      e

# the code finds an id exactly when the spec has it
def bs.held_has(+id: Nat, hs: List<&2, B.Hold>) -> {B.held(id, hs) == S.has(id, hs) : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case B.Hold{i, x}:
          bs.held_is(Nat.is_eq(i, id), B.held(id, t), S.has(id, t), bs.held_has(id, t))

# what the spec says of an id, the code's walk says
def bs.found(+id: Nat, +hs: List<&2, B.Hold>, -b: Bool, e: {S.has(id, hs) == b : Bool}) -> {b == B.held(id, hs) : Bool}:
  Equal.sym(Bool, B.held(id, hs), b, Equal.trans(Bool, B.held(id, hs), S.has(id, hs), b, bs.held_has(id, hs), e))

def bs.owed_one(same: Bool, +d: B.Dim, +x: B.Amt, +rest: B.Amt, -r: Nat, e: {S.at(d, rest) == r : Nat}) -> {S.at(d, B.owed.add(same, x, rest)) == S.held_of.one(same, S.at(d, x), r) : Nat}:
  match same:
    case True{}:
      %e : {S.at(d, B.add4(x, rest)) == Nat.add(S.at(d, x), _) : Nat}
      bs.at_add4(d, x, rest)
    case False{}:
      e

# what the code adds up under an id is what the id holds
def bs.owed_at(+id: Nat, +d: B.Dim, hs: List<&2, B.Hold>) -> {S.at(d, B.owed(id, hs)) == S.held_of(id, d, hs) : Nat}:
  match hs:
    case Nil{}:
      bs.at_zero(d)
    case Con{h, +t}:
      match h:
        case B.Hold{i, x}:
          bs.owed_one(Nat.is_eq(i, id), d, x, B.owed(id, t), S.held_of(id, d, t), bs.owed_at(id, d, t))

def bs.split_one(same: Bool, +d: B.Dim, -i: Nat, +x: B.Amt, +rest: List<&2, B.Hold>, -h: Nat, +ho: Nat, e: {Nat.add(ho, S.held(d, rest)) == h : Nat}) -> {Nat.add(S.held_of.one(same, S.at(d, x), ho), S.held(d, B.others.keep(same, B.Hold{i, x}, rest))) == Nat.add(S.at(d, x), h) : Nat}:
  match same:
    case True{}:
      %e : {Nat.add(Nat.add(S.at(d, x), ho), S.held(d, rest)) == Nat.add(S.at(d, x), _) : Nat}
      bs.add_assoc(S.at(d, x), ho, S.held(d, rest))
    case False{}:
      %e : {Nat.add(ho, Nat.add(S.at(d, x), S.held(d, rest))) == Nat.add(S.at(d, x), _) : Nat}
      bs.add_lcomm(ho, S.at(d, x), S.held(d, rest))

# what is held is what the id holds and what the others hold
def bs.held_split(+id: Nat, +d: B.Dim, hs: List<&2, B.Hold>) -> {Nat.add(S.held_of(id, d, hs), S.held(d, B.others(id, hs))) == S.held(d, hs) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      match h:
        case B.Hold{i, +x}:
          bs.split_one(Nat.is_eq(i, id), d, i, x, B.others(id, t), S.held(d, t), S.held_of(id, d, t), bs.held_split(id, d, t))

def bs.gone_one(same: Bool, -id: Nat, -i: Nat, -x: B.Amt, -rest: List<&2, B.Hold>, e: {same == Nat.is_eq(i, id) : Bool}, ih: {S.has(id, rest) == False{} : Bool}) -> {S.has(id, B.others.keep(same, B.Hold{i, x}, rest)) == False{} : Bool}:
  match same:
    case True{}:
      ih
    case False{}:
      %e : {Bool.or(_, S.has(id, rest)) == False{} : Bool}
      ih

# the others do not hold the id
def bs.others_has(+id: Nat, hs: List<&2, B.Hold>) -> {S.has(id, B.others(id, hs)) == False{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case B.Hold{i, x}:
          bs.gone_one(Nat.is_eq(i, id), id, i, x, B.others(id, t), {==}, bs.others_has(id, t))

def bs.kept_one(same: Bool, +j: Nat, +id: Nat, -d: B.Dim, +i: Nat, -x: B.Amt, -rest: List<&2, B.Hold>, -r: Nat, e: {Nat.is_eq(i, id) == same : Bool}, ne: {Nat.is_eq(j, id) == False{} : Bool}, ih: {S.held_of(j, d, rest) == r : Nat}) -> {S.held_of(j, d, B.others.keep(same, B.Hold{i, x}, rest)) == S.held_of.one(Nat.is_eq(i, j), S.at(d, x), r) : Nat}:
  match same:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(i, j), False{}, bs.eq_other(i, j, id, e, ne)) : {S.held_of(j, d, rest) == S.held_of.one(_, S.at(d, x), r) : Nat}
      ih
    case False{}:
      %ih : {S.held_of.one(Nat.is_eq(i, j), S.at(d, x), S.held_of(j, d, rest)) == S.held_of.one(Nat.is_eq(i, j), S.at(d, x), _) : Nat}
      {==}

# the others hold under another id what all the holds do
def bs.others_held_of(+j: Nat, +id: Nat, +d: B.Dim, hs: List<&2, B.Hold>, +ne: {Nat.is_eq(j, id) == False{} : Bool}) -> {S.held_of(j, d, B.others(id, hs)) == S.held_of(j, d, hs) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case B.Hold{+i, x}:
          bs.kept_one(Nat.is_eq(i, id), j, id, d, i, x, B.others(id, t), S.held_of(j, d, t), {==}, ne, bs.others_held_of(j, id, d, t, ne))

# what a settlement leaves free: free and the hold, less the spend
def bs.at_free(+d: B.Dim, +id: Nat, +f: B.Amt, +hs: List<&2, B.Hold>, +act: B.Amt) -> {Nat.sub(Nat.add(S.at(d, f), S.held_of(id, d, hs)), S.at(d, act)) == S.at(d, B.sub4(B.add4(f, B.owed(id, hs)), act)) : Nat}:
  %bs.owed_at(id, d, hs) : {Nat.sub(Nat.add(S.at(d, f), _), S.at(d, act)) == S.at(d, B.sub4(B.add4(f, B.owed(id, hs)), act)) : Nat}
  %bs.at_add4(d, f, B.owed(id, hs)) : {Nat.sub(_, S.at(d, act)) == S.at(d, B.sub4(B.add4(f, B.owed(id, hs)), act)) : Nat}
  bs.sub4_at(d, B.add4(f, B.owed(id, hs)), act)

# the overrun after a settlement: the spend past free and the hold
def bs.at_over(+d: B.Dim, +id: Nat, +o: B.Amt, +act: B.Amt, +f: B.Amt, +hs: List<&2, B.Hold>) -> {Nat.add(S.at(d, o), Nat.sub(S.at(d, act), Nat.add(S.at(d, f), S.held_of(id, d, hs)))) == S.at(d, B.add4(o, B.sub4(act, B.add4(f, B.owed(id, hs))))) : Nat}:
  %bs.owed_at(id, d, hs) : {Nat.add(S.at(d, o), Nat.sub(S.at(d, act), Nat.add(S.at(d, f), _))) == S.at(d, B.add4(o, B.sub4(act, B.add4(f, B.owed(id, hs))))) : Nat}
  %bs.at_add4(d, f, B.owed(id, hs)) : {Nat.add(S.at(d, o), Nat.sub(S.at(d, act), _)) == S.at(d, B.add4(o, B.sub4(act, B.add4(f, B.owed(id, hs))))) : Nat}
  %bs.at_sub4(d, act, B.add4(f, B.owed(id, hs))) : {Nat.add(S.at(d, o), _) == S.at(d, B.add4(o, B.sub4(act, B.add4(f, B.owed(id, hs))))) : Nat}
  bs.add4_at(d, o, B.sub4(act, B.add4(f, B.owed(id, hs))))

# Sums the laws need
# ------------------

def bs.mid(+sp: Nat, +a: Nat, -l: Nat) -> {Nat.add(a, Nat.add(sp, l)) == Nat.add(Nat.add(sp, a), l) : Nat}:
  %bs.add_assoc_r(sp, a, l) : {Nat.add(a, Nat.add(sp, l)) == _ : Nat}
  bs.add_lcomm(a, sp, l)

# the spend a moves out of spent, next to what is free
def bs.out(+m: Nat, +r: Nat, +sp: Nat, +a: Nat, +l: Nat) -> {Nat.add(Nat.add(m, a), Nat.add(r, Nat.add(sp, l))) == Nat.add(m, Nat.add(r, Nat.add(Nat.add(sp, a), l))) : Nat}:
  %bs.mid(sp, a, l) : {Nat.add(Nat.add(m, a), Nat.add(r, Nat.add(sp, l))) == Nat.add(m, Nat.add(r, _)) : Nat}
  %bs.add_lcomm(a, r, Nat.add(sp, l)) : {Nat.add(Nat.add(m, a), Nat.add(r, Nat.add(sp, l))) == Nat.add(m, _) : Nat}
  bs.add_assoc(m, a, Nat.add(r, Nat.add(sp, l)))

# the hold w moves out of what is held, next to what is free
def bs.in(+f: Nat, +w: Nat, +r: Nat, +x: Nat) -> {Nat.add(Nat.add(f, w), Nat.add(r, x)) == Nat.add(f, Nat.add(Nat.add(w, r), x)) : Nat}:
  %bs.add_assoc_r(w, r, x) : {Nat.add(Nat.add(f, w), Nat.add(r, x)) == Nat.add(f, _) : Nat}
  bs.add_assoc(f, w, Nat.add(r, x))

def bs.tail(+q: Nat, +y: Nat, +o: Nat, +m: Nat) -> {Nat.add(Nat.add(q, y), Nat.add(o, m)) == Nat.add(Nat.add(Nat.add(q, m), y), o) : Nat}:
  %bs.add_comm(m, o) : {Nat.add(Nat.add(q, y), _) == Nat.add(Nat.add(Nat.add(q, m), y), o) : Nat}
  %bs.add_assoc(Nat.add(q, y), m, o) : {_ == Nat.add(Nat.add(Nat.add(q, m), y), o) : Nat}
  %bs.add_rswap(q, m, y) : {Nat.add(_, o) == Nat.add(Nat.add(Nat.add(q, m), y), o) : Nat}
  {==}

# a settlement in one dimension: free f, the hold w, the other holds r,
# the spend a, spent sp, lent l, the overrun o
def bs.conserve_nat(+f: Nat, +w: Nat, +r: Nat, +a: Nat, +sp: Nat, +l: Nat, +o: Nat) -> {Nat.add(Nat.add(Nat.sub(Nat.add(f, w), a), Nat.add(r, Nat.add(Nat.add(sp, a), l))), o) == Nat.add(Nat.add(f, Nat.add(Nat.add(w, r), Nat.add(sp, l))), Nat.add(o, Nat.sub(a, Nat.add(f, w)))) : Nat}:
  %bs.out(Nat.sub(Nat.add(f, w), a), r, sp, a, l) : {Nat.add(_, o) == Nat.add(Nat.add(f, Nat.add(Nat.add(w, r), Nat.add(sp, l))), Nat.add(o, Nat.sub(a, Nat.add(f, w)))) : Nat}
  %bs.max(Nat.add(f, w), a) : {Nat.add(Nat.add(_, Nat.add(r, Nat.add(sp, l))), o) == Nat.add(Nat.add(f, Nat.add(Nat.add(w, r), Nat.add(sp, l))), Nat.add(o, Nat.sub(a, Nat.add(f, w)))) : Nat}
  %bs.tail(Nat.add(f, w), Nat.add(r, Nat.add(sp, l)), o, Nat.sub(a, Nat.add(f, w))) : {_ == Nat.add(Nat.add(f, Nat.add(Nat.add(w, r), Nat.add(sp, l))), Nat.add(o, Nat.sub(a, Nat.add(f, w)))) : Nat}
  %bs.in(f, w, r, Nat.add(sp, l)) : {Nat.add(Nat.add(Nat.add(f, w), Nat.add(r, Nat.add(sp, l))), Nat.add(o, Nat.sub(a, Nat.add(f, w)))) == Nat.add(_, Nat.add(o, Nat.sub(a, Nat.add(f, w)))) : Nat}
  {==}

# a spend a within the hold w: no overrun, and the rest is free
def bs.within_nat(+f: Nat, +w: Nat, +a: Nat, +o: Nat, e: {Nat.is_le(a, w) == True{} : Bool}) -> {Nat.add(o, Nat.sub(a, Nat.add(f, w))) == o : Nat} & {Nat.add(Nat.sub(Nat.add(f, w), a), a) == Nat.add(f, w) : Nat}:
  %bs.max(Nat.add(f, w), a) : {Nat.add(o, Nat.sub(a, Nat.add(f, w))) == o : Nat} & {_ == Nat.add(f, w) : Nat}
  %Equal.sym(Nat, Nat.sub(a, Nat.add(f, w)), 0n, bs.sub_none(a, f, w, e)) : {Nat.add(o, _) == o : Nat} & {Nat.add(Nat.add(f, w), _) == Nat.add(f, w) : Nat}
  (bs.add_zero(o), bs.add_zero(Nat.add(f, w)))

# funding n on free f, the overrun o, the rest of the budget t
def bs.fund_nat(+f: Nat, +n: Nat, +o: Nat, +t: Nat) -> {Nat.add(Nat.add(Nat.add(f, Nat.sub(n, o)), t), o) == Nat.add(Nat.add(Nat.add(f, t), n), Nat.sub(o, n)) : Nat}:
  %bs.add_rswap(f, t, Nat.sub(n, o)) : {Nat.add(_, o) == Nat.add(Nat.add(Nat.add(f, t), n), Nat.sub(o, n)) : Nat}
  %bs.add_assoc_r(Nat.add(f, t), Nat.sub(n, o), o) : {_ == Nat.add(Nat.add(Nat.add(f, t), n), Nat.sub(o, n)) : Nat}
  %bs.max(n, o) : {Nat.add(Nat.add(f, t), _) == Nat.add(Nat.add(Nat.add(f, t), n), Nat.sub(o, n)) : Nat}
  bs.add_assoc_r(Nat.add(f, t), n, Nat.sub(o, n))

# Settle
# ------

# settling an id that is not held changes nothing
def bs.inert(+id: Nat, -act: B.Amt, a: B.Acct, miss: {S.has(id, S.holds(a)) == False{} : Bool}) -> {B.settle(id, act, a) == a : B.Acct}:
  match a:
    case B.Acct{f, s, l, o, +hs, u}:
      %bs.found(id, hs, False{}, miss) : {B.settle.if(_, id, act, f, s, l, o, hs, u) == B.Acct{f, s, l, o, hs, u} : B.Acct}
      {==}

# settling a held id: free and the hold pay the spend, the others stay
def bs.open(+id: Nat, -act: B.Amt, -f: B.Amt, -s: B.Amt, -l: B.Amt, -o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, open: {S.has(id, hs) == True{} : Bool}) -> {B.settle.take(B.add4(f, B.owed(id, hs)), act, s, l, o, B.others(id, hs), u) == B.settle(id, act, B.Acct{f, s, l, o, hs, u}) : B.Acct}:
  %bs.found(id, hs, True{}, open) : {B.settle.take(B.add4(f, B.owed(id, hs)), act, s, l, o, B.others(id, hs), u) == B.settle.if(_, id, act, f, s, l, o, hs, u) : B.Acct}
  {==}

def bs.settled_if(h: Bool, +id: Nat, -act: B.Amt, -f: B.Amt, -s: B.Amt, -l: B.Amt, -o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, e: {h == B.held(id, hs) : Bool}) -> {S.has(id, S.holds(B.settle.if(h, id, act, f, s, l, o, hs, u))) == False{} : Bool}:
  match h:
    case True{}:
      bs.others_has(id, hs)
    case False{}:
      %bs.held_has(id, hs) : {_ == False{} : Bool}
      %e : {_ == False{} : Bool}
      {==}

# after a settlement the id is not held
def bs.settled(+id: Nat, -act: B.Amt, a: B.Acct) -> {S.has(id, S.holds(B.settle(id, act, a))) == False{} : Bool}:
  match a:
    case B.Acct{f, s, l, o, +hs, u}:
      bs.settled_if(B.held(id, hs), id, act, f, s, l, o, hs, u, {==})

def bs.conserve_if(h: Bool, +id: Nat, +act: B.Amt, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, +d: B.Dim) -> {Nat.add(S.net(d, B.settle.if(h, id, act, f, s, l, o, hs, u)), S.at(d, o)) == Nat.add(S.net(d, B.Acct{f, s, l, o, hs, u}), S.at(d, S.over(B.settle.if(h, id, act, f, s, l, o, hs, u)))) : Nat}:
  match h:
    case True{}:
      %bs.at_free(d, id, f, hs, act) : {Nat.add(Nat.add(_, Nat.add(S.held(d, B.others(id, hs)), Nat.add(S.at(d, B.add4(s, act)), S.at(d, l)))), S.at(d, o)) == Nat.add(Nat.add(S.at(d, f), Nat.add(S.held(d, hs), Nat.add(S.at(d, s), S.at(d, l)))), S.at(d, B.add4(o, B.sub4(act, B.add4(f, B.owed(id, hs)))))) : Nat}
      %bs.add4_at(d, s, act) : {Nat.add(Nat.add(Nat.sub(Nat.add(S.at(d, f), S.held_of(id, d, hs)), S.at(d, act)), Nat.add(S.held(d, B.others(id, hs)), Nat.add(_, S.at(d, l)))), S.at(d, o)) == Nat.add(Nat.add(S.at(d, f), Nat.add(S.held(d, hs), Nat.add(S.at(d, s), S.at(d, l)))), S.at(d, B.add4(o, B.sub4(act, B.add4(f, B.owed(id, hs)))))) : Nat}
      %bs.held_split(id, d, hs) : {Nat.add(Nat.add(Nat.sub(Nat.add(S.at(d, f), S.held_of(id, d, hs)), S.at(d, act)), Nat.add(S.held(d, B.others(id, hs)), Nat.add(Nat.add(S.at(d, s), S.at(d, act)), S.at(d, l)))), S.at(d, o)) == Nat.add(Nat.add(S.at(d, f), Nat.add(_, Nat.add(S.at(d, s), S.at(d, l)))), S.at(d, B.add4(o, B.sub4(act, B.add4(f, B.owed(id, hs)))))) : Nat}
      %bs.at_over(d, id, o, act, f, hs) : {Nat.add(Nat.add(Nat.sub(Nat.add(S.at(d, f), S.held_of(id, d, hs)), S.at(d, act)), Nat.add(S.held(d, B.others(id, hs)), Nat.add(Nat.add(S.at(d, s), S.at(d, act)), S.at(d, l)))), S.at(d, o)) == Nat.add(Nat.add(S.at(d, f), Nat.add(Nat.add(S.held_of(id, d, hs), S.held(d, B.others(id, hs))), Nat.add(S.at(d, s), S.at(d, l)))), _) : Nat}
      bs.conserve_nat(S.at(d, f), S.held_of(id, d, hs), S.held(d, B.others(id, hs)), S.at(d, act), S.at(d, s), S.at(d, l), S.at(d, o))
    case False{}:
      {==}

def bs.keeps_if(h: Bool, +j: Nat, +id: Nat, -act: B.Amt, -f: B.Amt, -s: B.Amt, -l: B.Amt, -o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, +d: B.Dim, +other: {Nat.is_eq(j, id) == False{} : Bool}) -> {S.held_of(j, d, S.holds(B.settle.if(h, id, act, f, s, l, o, hs, u))) == S.held_of(j, d, hs) : Nat}:
  match h:
    case True{}:
      bs.others_held_of(j, id, d, hs, other)
    case False{}:
      {==}

# settling a held id charges the spend, leaves no hold under the id and
# keeps lent and the deadline
def bs.charges(+id: Nat, +act: B.Amt, -f: B.Amt, +s: B.Amt, -l: B.Amt, -o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, +d: B.Dim, open: {S.has(id, hs) == True{} : Bool}) -> {S.at(d, S.spent(B.settle(id, act, B.Acct{f, s, l, o, hs, u}))) == Nat.add(S.at(d, s), S.at(d, act)) : Nat} & {S.has(id, S.holds(B.settle(id, act, B.Acct{f, s, l, o, hs, u}))) == False{} : Bool} & {S.lent(B.settle(id, act, B.Acct{f, s, l, o, hs, u})) == l : B.Amt} & {S.until(B.settle(id, act, B.Acct{f, s, l, o, hs, u})) == u : Nat}:
  %bs.open(id, act, f, s, l, o, hs, u, open) : {S.at(d, S.spent(_)) == Nat.add(S.at(d, s), S.at(d, act)) : Nat} & {S.has(id, S.holds(_)) == False{} : Bool} & {S.lent(_) == l : B.Amt} & {S.until(_) == u : Nat}
  (bs.at_add4(d, s, act), (bs.others_has(id, hs), ({==}, {==})))

# a spend within the hold makes no overrun and frees the rest
def bs.within(+id: Nat, +act: B.Amt, +f: B.Amt, -s: B.Amt, -l: B.Amt, +o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, +d: B.Dim, open: {S.has(id, hs) == True{} : Bool}, within: {Nat.is_le(S.at(d, act), S.held_of(id, d, hs)) == True{} : Bool}) -> {S.at(d, S.over(B.settle(id, act, B.Acct{f, s, l, o, hs, u}))) == S.at(d, o) : Nat} & {Nat.add(S.at(d, S.free(B.settle(id, act, B.Acct{f, s, l, o, hs, u}))), S.at(d, act)) == Nat.add(S.at(d, f), S.held_of(id, d, hs)) : Nat}:
  %bs.open(id, act, f, s, l, o, hs, u, open) : {S.at(d, S.over(_)) == S.at(d, o) : Nat} & {Nat.add(S.at(d, S.free(_)), S.at(d, act)) == Nat.add(S.at(d, f), S.held_of(id, d, hs)) : Nat}
  %bs.at_over(d, id, o, act, f, hs) : {_ == S.at(d, o) : Nat} & {Nat.add(S.at(d, B.sub4(B.add4(f, B.owed(id, hs)), act)), S.at(d, act)) == Nat.add(S.at(d, f), S.held_of(id, d, hs)) : Nat}
  %bs.at_free(d, id, f, hs, act) : {Nat.add(S.at(d, o), Nat.sub(S.at(d, act), Nat.add(S.at(d, f), S.held_of(id, d, hs)))) == S.at(d, o) : Nat} & {Nat.add(_, S.at(d, act)) == Nat.add(S.at(d, f), S.held_of(id, d, hs)) : Nat}
  bs.within_nat(S.at(d, f), S.held_of(id, d, hs), S.at(d, act), S.at(d, o), within)

# a hold settled at what it holds: all of it is spent, free and the
# overrun stay
def bs.recover(+id: Nat, +act: B.Amt, +f: B.Amt, +s: B.Amt, -l: B.Amt, +o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, +d: B.Dim, open: {S.has(id, hs) == True{} : Bool}, full: {S.at(d, act) == S.held_of(id, d, hs) : Nat}) -> {S.at(d, S.spent(B.settle(id, act, B.Acct{f, s, l, o, hs, u}))) == Nat.add(S.at(d, s), S.held_of(id, d, hs)) : Nat} & {S.at(d, S.free(B.settle(id, act, B.Acct{f, s, l, o, hs, u}))) == S.at(d, f) : Nat} & {S.at(d, S.over(B.settle(id, act, B.Acct{f, s, l, o, hs, u}))) == S.at(d, o) : Nat}:
  %bs.open(id, act, f, s, l, o, hs, u, open) : {S.at(d, S.spent(_)) == Nat.add(S.at(d, s), S.held_of(id, d, hs)) : Nat} & {S.at(d, S.free(_)) == S.at(d, f) : Nat} & {S.at(d, S.over(_)) == S.at(d, o) : Nat}
  %bs.at_free(d, id, f, hs, act) : {S.at(d, B.add4(s, act)) == Nat.add(S.at(d, s), S.held_of(id, d, hs)) : Nat} & {_ == S.at(d, f) : Nat} & {S.at(d, B.add4(o, B.sub4(act, B.add4(f, B.owed(id, hs))))) == S.at(d, o) : Nat}
  %bs.at_over(d, id, o, act, f, hs) : {S.at(d, B.add4(s, act)) == Nat.add(S.at(d, s), S.held_of(id, d, hs)) : Nat} & {Nat.sub(Nat.add(S.at(d, f), S.held_of(id, d, hs)), S.at(d, act)) == S.at(d, f) : Nat} & {_ == S.at(d, o) : Nat}
  %full : {S.at(d, B.add4(s, act)) == Nat.add(S.at(d, s), _) : Nat} & {Nat.sub(Nat.add(S.at(d, f), _), S.at(d, act)) == S.at(d, f) : Nat} & {Nat.add(S.at(d, o), Nat.sub(S.at(d, act), Nat.add(S.at(d, f), _))) == S.at(d, o) : Nat}
  (bs.at_add4(d, s, act), (bs.sub_add_r(S.at(d, f), S.at(d, act)), bs.over_full(S.at(d, o), S.at(d, f), S.at(d, act))))

# Fund
# ----

# funding n adds n to the budget, what repays the overrun included
def bs.fund_net(+n: B.Amt, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, -u2: Nat, +d: B.Dim) -> {Nat.add(S.net(d, B.Acct{B.add4(f, B.sub4(n, o)), s, l, B.sub4(o, n), hs, u2}), S.at(d, o)) == Nat.add(Nat.add(S.net(d, B.Acct{f, s, l, o, hs, u}), S.at(d, n)), S.at(d, B.sub4(o, n))) : Nat}:
  %bs.sub4_at(d, o, n) : {Nat.add(Nat.add(S.at(d, B.add4(f, B.sub4(n, o))), Nat.add(S.held(d, hs), Nat.add(S.at(d, s), S.at(d, l)))), S.at(d, o)) == Nat.add(Nat.add(Nat.add(S.at(d, f), Nat.add(S.held(d, hs), Nat.add(S.at(d, s), S.at(d, l)))), S.at(d, n)), _) : Nat}
  %bs.add4_at(d, f, B.sub4(n, o)) : {Nat.add(Nat.add(_, Nat.add(S.held(d, hs), Nat.add(S.at(d, s), S.at(d, l)))), S.at(d, o)) == Nat.add(Nat.add(Nat.add(S.at(d, f), Nat.add(S.held(d, hs), Nat.add(S.at(d, s), S.at(d, l)))), S.at(d, n)), Nat.sub(S.at(d, o), S.at(d, n))) : Nat}
  %bs.sub4_at(d, n, o) : {Nat.add(Nat.add(Nat.add(S.at(d, f), _), Nat.add(S.held(d, hs), Nat.add(S.at(d, s), S.at(d, l)))), S.at(d, o)) == Nat.add(Nat.add(Nat.add(S.at(d, f), Nat.add(S.held(d, hs), Nat.add(S.at(d, s), S.at(d, l)))), S.at(d, n)), Nat.sub(S.at(d, o), S.at(d, n))) : Nat}
  bs.fund_nat(S.at(d, f), S.at(d, n), S.at(d, o), Nat.add(S.held(d, hs), Nat.add(S.at(d, s), S.at(d, l))))

# a settlement of a held id: free and the hold less the spend are free,
# the spend past them is added to the overrun
def bs.from_free(+id: Nat, +act: B.Amt, +f: B.Amt, -s: B.Amt, -l: B.Amt, +o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, +d: B.Dim, open: {S.has(id, hs) == True{} : Bool}) -> {S.at(d, S.free(B.settle(id, act, B.Acct{f, s, l, o, hs, u}))) == Nat.sub(Nat.add(S.at(d, f), S.held_of(id, d, hs)), S.at(d, act)) : Nat} & {S.at(d, S.over(B.settle(id, act, B.Acct{f, s, l, o, hs, u}))) == Nat.add(S.at(d, o), Nat.sub(S.at(d, act), Nat.add(S.at(d, f), S.held_of(id, d, hs)))) : Nat}:
  %bs.open(id, act, f, s, l, o, hs, u, open) : {S.at(d, S.free(_)) == Nat.sub(Nat.add(S.at(d, f), S.held_of(id, d, hs)), S.at(d, act)) : Nat} & {S.at(d, S.over(_)) == Nat.add(S.at(d, o), Nat.sub(S.at(d, act), Nat.add(S.at(d, f), S.held_of(id, d, hs)))) : Nat}
  (Equal.sym(Nat, Nat.sub(Nat.add(S.at(d, f), S.held_of(id, d, hs)), S.at(d, act)), S.at(d, B.sub4(B.add4(f, B.owed(id, hs)), act)), bs.at_free(d, id, f, hs, act)), Equal.sym(Nat, Nat.add(S.at(d, o), Nat.sub(S.at(d, act), Nat.add(S.at(d, f), S.held_of(id, d, hs)))), S.at(d, B.add4(o, B.sub4(act, B.add4(f, B.owed(id, hs))))), bs.at_over(d, id, o, act, f, hs)))

def bs.kept_has(same: Bool, +j: Nat, +id: Nat, +i: Nat, -x: B.Amt, -rest: List<&2, B.Hold>, -r: Bool, e: {Nat.is_eq(i, id) == same : Bool}, ne: {Nat.is_eq(j, id) == False{} : Bool}, ih: {S.has(j, rest) == r : Bool}) -> {S.has(j, B.others.keep(same, B.Hold{i, x}, rest)) == Bool.or(Nat.is_eq(i, j), r) : Bool}:
  match same:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(i, j), False{}, bs.eq_other(i, j, id, e, ne)) : {S.has(j, rest) == Bool.or(_, r) : Bool}
      ih
    case False{}:
      %ih : {Bool.or(Nat.is_eq(i, j), S.has(j, rest)) == Bool.or(Nat.is_eq(i, j), _) : Bool}
      {==}

# the others hold another id exactly when all the holds do
def bs.others_has_j(+j: Nat, +id: Nat, hs: List<&2, B.Hold>, +ne: {Nat.is_eq(j, id) == False{} : Bool}) -> {S.has(j, B.others(id, hs)) == S.has(j, hs) : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case B.Hold{+i, x}:
          bs.kept_has(Nat.is_eq(i, id), j, id, i, x, B.others(id, t), S.has(j, t), {==}, ne, bs.others_has_j(j, id, t, ne))

def bs.keeps_ids_if(h: Bool, +j: Nat, +id: Nat, -act: B.Amt, -f: B.Amt, -s: B.Amt, -l: B.Amt, -o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, +other: {Nat.is_eq(j, id) == False{} : Bool}) -> {S.has(j, S.holds(B.settle.if(h, id, act, f, s, l, o, hs, u))) == S.has(j, hs) : Bool}:
  match h:
    case True{}:
      bs.others_has_j(j, id, hs, other)
    case False{}:
      {==}

# funding x frees what is past the overrun o
def bs.repays(+x: B.Amt, +f: B.Amt, +o: B.Amt, +d: B.Dim) -> {S.at(d, B.add4(f, B.sub4(x, o))) == Nat.add(S.at(d, f), Nat.sub(S.at(d, x), S.at(d, o))) : Nat}:
  %bs.at_sub4(d, x, o) : {S.at(d, B.add4(f, B.sub4(x, o))) == Nat.add(S.at(d, f), _) : Nat}
  bs.at_add4(d, f, B.sub4(x, o))
