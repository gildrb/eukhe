# eukhe: digit-list naturals (bend/autoresearch/stats.bend big.*) for the
# proof of LAW confidence_exact: what sums, differences, comparisons and
# reversed decimal digits are worth (big.val), and that they stay digits

import Base
import ../../../../bend/autoresearch/dec.bend as ArD
import ../../../../bend/autoresearch/state.bend as ArS
import ../../../../bend/autoresearch/stats.bend as ArT
import ../../../../spec/autoresearch/decimal.bend as SD
import ./nat.bend as CN

# Digits
# ------

def ac.dok_hd(+x: Nat, -t: List<&2, Nat>, +h: {SD.digits_ok(x <> t) == True{} : Bool}) -> {Nat.is_lt(x, 10n) == True{} : Bool}:
  CN.ac.and_l(Nat.is_lt(x, 10n), SD.digits_ok(t), h)

def ac.dok_tl(+x: Nat, -t: List<&2, Nat>, +h: {SD.digits_ok(x <> t) == True{} : Bool}) -> {SD.digits_ok(t) == True{} : Bool}:
  CN.ac.and_r(Nat.is_lt(x, 10n), SD.digits_ok(t), h)

def ac.dok_cons(-x: Nat, -t: List<&2, Nat>, +hx: {Nat.is_lt(x, 10n) == True{} : Bool}, +ht: {SD.digits_ok(t) == True{} : Bool}) -> {SD.digits_ok(x <> t) == True{} : Bool}:
  CN.ac.and_i(Nat.is_lt(x, 10n), SD.digits_ok(t), hx, ht)

def ac.lt10_le9(+y: Nat, +h: {Nat.is_lt(y, 10n) == True{} : Bool}) -> {Nat.is_le(y, 9n) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(y, 9n), Nat.is_lt(y, 10n), CN.ac.le_lt_succ(y, 9n)) : {_ == True{} : Bool}
  h

# Division by 10
# --------------

def ac.dm10(+s: Nat) -> {Nat.add(Nat.mod(s, 10n), Nat.mul(Nat.div(s, 10n), 10n)) == s : Nat}:
  %CN.ac.add_comm(Nat.mul(Nat.div(s, 10n), 10n), Nat.mod(s, 10n)) : {_ == s : Nat}
  CN.ac.div_eq(s, 9n)

def ac.mod10(+s: Nat) -> {Nat.is_lt(Nat.mod(s, 10n), 10n) == True{} : Bool}:
  %CN.ac.le_lt_succ(Nat.mod(s, 10n), 9n) : {_ == True{} : Bool}
  CN.ac.mod_le(s, 9n)

def ac.carry1.go(+q: Nat, +r: Nat, -s: Nat, +e: {Nat.add(Nat.mul(q, 10n), r) == s : Nat}, +h: {Nat.is_lt(s, 20n) == True{} : Bool}) -> {Nat.is_le(q, 1n) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n++p:
      match p:
        case 0n:
          {==}
        case 1n++u:
          +h2 = {%Equal.sym(Nat, Nat.add(Nat.mul(2n+u, 10n), r), s, e) : {Nat.is_lt(_, 20n) == True{} : Bool}; h : {Nat.is_lt(Nat.add(Nat.mul(2n+u, 10n), r), 20n) == True{} : Bool}}
          CN.ac.lt0({Nat.is_le(2n+u, 1n) == True{} : Bool}, Nat.add(Nat.mul(u, 10n), r), h2)

# a carry out of a sum below 20 is at most 1
def ac.carry1(+s: Nat, +h: {Nat.is_lt(s, 20n) == True{} : Bool}) -> {Nat.is_le(Nat.div(s, 10n), 1n) == True{} : Bool}:
  ac.carry1.go(Nat.div(s, 10n), Nat.mod(s, 10n), s, CN.ac.div_eq(s, 9n), h)

# two digits and a carry of at most 1 add up to less than 20
def ac.sum20(+x: Nat, +y: Nat, +c: Nat, +hx: {Nat.is_lt(x, 10n) == True{} : Bool}, +hy: {Nat.is_lt(y, 10n) == True{} : Bool}, +hc: {Nat.is_le(c, 1n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(x, Nat.add(y, c)), 20n) == True{} : Bool}:
  +yc = CN.ac.le_add_mono(y, 9n, c, 1n, ac.lt10_le9(y, hy), hc)
  +xyc = CN.ac.le_add_mono(x, 9n, Nat.add(y, c), 10n, ac.lt10_le9(x, hx), yc)
  %CN.ac.le_lt_succ(Nat.add(x, Nat.add(y, c)), 19n) : {_ == True{} : Bool}
  xyc

# Sums
# ----

def ac.val_last(+c: Nat) -> {ArT.big.val(ArT.big.add.last(c)) == c : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++p:
      %CN.ac.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# a digit and a carry over: mod s + 10 (V + div s) = s + 10 V
def ac.vstep(+s: Nat, +V: Nat) -> {Nat.add(Nat.mod(s, 10n), Nat.mul(Nat.add(V, Nat.div(s, 10n)), 10n)) == Nat.add(s, Nat.mul(V, 10n)) : Nat}:
  +m = Nat.mod(s, 10n)
  +d = Nat.div(s, 10n)
  +MV = Nat.mul(V, 10n)
  +Md = Nat.mul(d, 10n)
  %Equal.sym(Nat, Nat.mul(Nat.add(V, d), 10n), Nat.add(MV, Md), CN.ac.mul_add(V, d, 10n)) : {Nat.add(m, _) == Nat.add(s, MV) : Nat}
  %CN.ac.add_swap(MV, m, Md) : {_ == Nat.add(s, MV) : Nat}
  %Equal.sym(Nat, Nat.add(m, Md), s, ac.dm10(s)) : {Nat.add(MV, _) == Nat.add(s, MV) : Nat}
  CN.ac.add_comm(MV, s)

# big.add is a + b + c
def ac.val_add(+a: List<&2, Nat>, +b: List<&2, Nat>, +c: Nat) -> {ArT.big.val(ArT.big.add(a, b, c)) == Nat.add(ArT.big.val(a), Nat.add(ArT.big.val(b), c)) : Nat}:
  match a b:
    case Nil{} Nil{}:
      ac.val_last(c)
    case Nil{} +y <> +yr:
      +s = Nat.add(y, c)
      +d = Nat.div(s, 10n)
      +V = ArT.big.val(yr)
      +rec = ArT.big.add(Nil{}, yr, d)
      +rhs = Nat.add(Nat.add(y, Nat.mul(V, 10n)), c)
      %Equal.sym(Nat, ArT.big.val(rec), Nat.add(V, d), ac.val_add(Nil{}, yr, d)) : {Nat.add(Nat.mod(s, 10n), Nat.mul(_, 10n)) == rhs : Nat}
      %Equal.sym(Nat, Nat.add(Nat.mod(s, 10n), Nat.mul(Nat.add(V, d), 10n)), Nat.add(s, Nat.mul(V, 10n)), ac.vstep(s, V)) : {_ == rhs : Nat}
      CN.ac.add_rcomm(y, c, Nat.mul(V, 10n))
    case +x <> +xr Nil{}:
      +s = Nat.add(x, c)
      +d = Nat.div(s, 10n)
      +V = ArT.big.val(xr)
      +rec = ArT.big.add(xr, Nil{}, d)
      +rhs = Nat.add(Nat.add(x, Nat.mul(V, 10n)), c)
      %Equal.sym(Nat, ArT.big.val(rec), Nat.add(V, d), ac.val_add(xr, Nil{}, d)) : {Nat.add(Nat.mod(s, 10n), Nat.mul(_, 10n)) == rhs : Nat}
      %Equal.sym(Nat, Nat.add(Nat.mod(s, 10n), Nat.mul(Nat.add(V, d), 10n)), Nat.add(s, Nat.mul(V, 10n)), ac.vstep(s, V)) : {_ == rhs : Nat}
      CN.ac.add_rcomm(x, c, Nat.mul(V, 10n))
    case +x <> +xr +y <> +yr:
      +s = Nat.add(x, Nat.add(y, c))
      +d = Nat.div(s, 10n)
      +Vx = ArT.big.val(xr)
      +Vy = ArT.big.val(yr)
      +V = Nat.add(Vx, Vy)
      +rec = ArT.big.add(xr, yr, d)
      +rhs = Nat.add(Nat.add(x, Nat.mul(Vx, 10n)), Nat.add(Nat.add(y, Nat.mul(Vy, 10n)), c))
      %Equal.sym(Nat, ArT.big.val(rec), Nat.add(Vx, Nat.add(Vy, d)), ac.val_add(xr, yr, d)) : {Nat.add(Nat.mod(s, 10n), Nat.mul(_, 10n)) == rhs : Nat}
      %CN.ac.add_assoc(Vx, Vy, d) : {Nat.add(Nat.mod(s, 10n), Nat.mul(_, 10n)) == rhs : Nat}
      %Equal.sym(Nat, Nat.add(Nat.mod(s, 10n), Nat.mul(Nat.add(V, d), 10n)), Nat.add(s, Nat.mul(V, 10n)), ac.vstep(s, V)) : {_ == rhs : Nat}
      %Equal.sym(Nat, Nat.mul(V, 10n), Nat.add(Nat.mul(Vx, 10n), Nat.mul(Vy, 10n)), CN.ac.mul_add(Vx, Vy, 10n)) : {Nat.add(s, _) == rhs : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(x, Nat.add(y, c)), Nat.add(Nat.mul(Vx, 10n), Nat.mul(Vy, 10n))), Nat.add(Nat.add(x, Nat.mul(Vx, 10n)), Nat.add(Nat.add(y, c), Nat.mul(Vy, 10n))), CN.ac.add_4(x, Nat.add(y, c), Nat.mul(Vx, 10n), Nat.mul(Vy, 10n))) : {_ == rhs : Nat}
      %CN.ac.add_rcomm(y, Nat.mul(Vy, 10n), c) : {Nat.add(Nat.add(x, Nat.mul(Vx, 10n)), _) == rhs : Nat}
      {==}

def ac.dok_last(+c: Nat, +h: {Nat.is_le(c, 1n) == True{} : Bool}) -> {SD.digits_ok(ArT.big.add.last(c)) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++p:
      match p:
        case 0n:
          {==}
        case 1n++q:
          CN.ac.ft({SD.digits_ok(ArT.big.add.last(2n+q)) == True{} : Bool}, h)

# a sum of digit lists with a carry of at most 1 is digits
def ac.dok_add(+a: List<&2, Nat>, +b: List<&2, Nat>, +c: Nat, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}, +hc: {Nat.is_le(c, 1n) == True{} : Bool}) -> {SD.digits_ok(ArT.big.add(a, b, c)) == True{} : Bool}:
  match a b:
    case Nil{} Nil{}:
      ac.dok_last(c, hc)
    case Nil{} +y <> +yr:
      +s = Nat.add(y, c)
      +rec = ArT.big.add(Nil{}, yr, Nat.div(s, 10n))
      ac.dok_cons(Nat.mod(s, 10n), rec, ac.mod10(s), ac.dok_add(Nil{}, yr, Nat.div(s, 10n), ha, ac.dok_tl(y, yr, hb), ac.carry1(s, ac.sum20(0n, y, c, {==}, ac.dok_hd(y, yr, hb), hc))))
    case +x <> +xr Nil{}:
      +s = Nat.add(x, c)
      +rec = ArT.big.add(xr, Nil{}, Nat.div(s, 10n))
      ac.dok_cons(Nat.mod(s, 10n), rec, ac.mod10(s), ac.dok_add(xr, Nil{}, Nat.div(s, 10n), ac.dok_tl(x, xr, ha), hb, ac.carry1(s, ac.sum20(x, 0n, c, ac.dok_hd(x, xr, ha), {==}, hc))))
    case +x <> +xr +y <> +yr:
      +s = Nat.add(x, Nat.add(y, c))
      +rec = ArT.big.add(xr, yr, Nat.div(s, 10n))
      ac.dok_cons(Nat.mod(s, 10n), rec, ac.mod10(s), ac.dok_add(xr, yr, Nat.div(s, 10n), ac.dok_tl(x, xr, ha), ac.dok_tl(y, yr, hb), ac.carry1(s, ac.sum20(x, y, c, ac.dok_hd(x, xr, ha), ac.dok_hd(y, yr, hb), hc))))

# Comparison
# ----------

def ac.then_eq(+c: Cmp) -> {ArD.then(c, EQ{}) == c : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def ac.then_assoc(+c: Cmp, -d: Cmp, -e: Cmp) -> {ArD.then(ArD.then(c, d), e) == ArD.then(c, ArD.then(d, e)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# x < k is below k + W
def ac.cmp_small(+x: Nat, +k: Nat, +W: Nat, +h: {Nat.is_lt(x, k) == True{} : Bool}) -> {Nat.cmp(x, Nat.add(k, W)) == LT{} : Cmp}:
  match x k:
    case x 0n:
      CN.ac.lt0({Nat.cmp(x, Nat.add(0n, W)) == LT{} : Cmp}, x, h)
    case 0n 1n++q:
      {==}
    case 1n++p 1n++q:
      ac.cmp_small(p, q, W, h)

def ac.cmp_large(+x: Nat, +k: Nat, +W: Nat, +h: {Nat.is_lt(x, k) == True{} : Bool}) -> {Nat.cmp(Nat.add(k, W), x) == GT{} : Cmp}:
  match x k:
    case x 0n:
      CN.ac.lt0({Nat.cmp(Nat.add(0n, W), x) == GT{} : Cmp}, x, h)
    case 0n 1n++q:
      {==}
    case 1n++p 1n++q:
      ac.cmp_large(p, q, W, h)

# two numbers of a last digit and the rest compare by the rest, then the
# digit
def ac.cmp_dig(+x: Nat, +y: Nat, +A: Nat, +B: Nat, +hx: {Nat.is_lt(x, 10n) == True{} : Bool}, +hy: {Nat.is_lt(y, 10n) == True{} : Bool}) -> {Nat.cmp(Nat.add(x, Nat.mul(A, 10n)), Nat.add(y, Nat.mul(B, 10n))) == ArD.then(Nat.cmp(A, B), Nat.cmp(x, y)) : Cmp}:
  match A B:
    case 0n 0n:
      %Equal.sym(Nat, Nat.add(x, 0n), x, CN.ac.add_zero(x)) : {Nat.cmp(_, Nat.add(y, 0n)) == Nat.cmp(x, y) : Cmp}
      %Equal.sym(Nat, Nat.add(y, 0n), y, CN.ac.add_zero(y)) : {Nat.cmp(x, _) == Nat.cmp(x, y) : Cmp}
      {==}
    case 0n 1n++b:
      +Mb = Nat.mul(b, 10n)
      %Equal.sym(Nat, Nat.add(x, 0n), x, CN.ac.add_zero(x)) : {Nat.cmp(_, Nat.add(y, Nat.add(10n, Mb))) == LT{} : Cmp}
      %CN.ac.add_swap(10n, y, Mb) : {Nat.cmp(x, _) == LT{} : Cmp}
      ac.cmp_small(x, 10n, Nat.add(y, Mb), hx)
    case 1n++a 0n:
      +Ma = Nat.mul(a, 10n)
      %Equal.sym(Nat, Nat.add(y, 0n), y, CN.ac.add_zero(y)) : {Nat.cmp(Nat.add(x, Nat.add(10n, Ma)), _) == GT{} : Cmp}
      %CN.ac.add_swap(10n, x, Ma) : {Nat.cmp(_, y) == GT{} : Cmp}
      ac.cmp_large(y, 10n, Nat.add(x, Ma), hy)
    case 1n++a 1n++b:
      +Ma = Nat.mul(a, 10n)
      +Mb = Nat.mul(b, 10n)
      +rhs = ArD.then(Nat.cmp(a, b), Nat.cmp(x, y))
      %CN.ac.add_swap(10n, x, Ma) : {Nat.cmp(_, Nat.add(y, Nat.add(10n, Mb))) == rhs : Cmp}
      %CN.ac.add_swap(10n, y, Mb) : {Nat.cmp(Nat.add(10n, Nat.add(x, Ma)), _) == rhs : Cmp}
      %Equal.sym(Cmp, Nat.cmp(Nat.add(10n, Nat.add(x, Ma)), Nat.add(10n, Nat.add(y, Mb))), Nat.cmp(Nat.add(x, Ma), Nat.add(y, Mb)), CN.ac.cmp_cancel(10n, Nat.add(x, Ma), Nat.add(y, Mb))) : {_ == rhs : Cmp}
      ac.cmp_dig(x, y, a, b, hx, hy)

# big.cmp(a, b, acc) is the order of their values, then acc
def ac.cmp_val(+a: List<&2, Nat>, +b: List<&2, Nat>, +acc: Cmp, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}) -> {ArT.big.cmp(a, b, acc) == ArD.then(Nat.cmp(ArT.big.val(a), ArT.big.val(b)), acc) : Cmp}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yr:
      +Vy = ArT.big.val(yr)
      +c1 = Nat.cmp(0n, Vy)
      +c2 = Nat.cmp(0n, y)
      +rhs = ArD.then(Nat.cmp(0n, Nat.add(y, Nat.mul(Vy, 10n))), acc)
      %Equal.sym(Cmp, ArT.big.cmp(Nil{}, yr, ArD.then(c2, acc)), ArD.then(c1, ArD.then(c2, acc)), ac.cmp_val(Nil{}, yr, ArD.then(c2, acc), ha, ac.dok_tl(y, yr, hb))) : {_ == rhs : Cmp}
      %Equal.sym(Cmp, Nat.cmp(0n, Nat.add(y, Nat.mul(Vy, 10n))), ArD.then(c1, c2), ac.cmp_dig(0n, y, 0n, Vy, {==}, ac.dok_hd(y, yr, hb))) : {ArD.then(c1, ArD.then(c2, acc)) == ArD.then(_, acc) : Cmp}
      Equal.sym(Cmp, ArD.then(ArD.then(c1, c2), acc), ArD.then(c1, ArD.then(c2, acc)), ac.then_assoc(c1, c2, acc))
    case +x <> +xr Nil{}:
      +Vx = ArT.big.val(xr)
      +c1 = Nat.cmp(Vx, 0n)
      +c2 = Nat.cmp(x, 0n)
      +rhs = ArD.then(Nat.cmp(Nat.add(x, Nat.mul(Vx, 10n)), 0n), acc)
      %Equal.sym(Cmp, ArT.big.cmp(xr, Nil{}, ArD.then(c2, acc)), ArD.then(c1, ArD.then(c2, acc)), ac.cmp_val(xr, Nil{}, ArD.then(c2, acc), ac.dok_tl(x, xr, ha), hb)) : {_ == rhs : Cmp}
      %Equal.sym(Cmp, Nat.cmp(Nat.add(x, Nat.mul(Vx, 10n)), 0n), ArD.then(c1, c2), ac.cmp_dig(x, 0n, Vx, 0n, ac.dok_hd(x, xr, ha), {==})) : {ArD.then(c1, ArD.then(c2, acc)) == ArD.then(_, acc) : Cmp}
      Equal.sym(Cmp, ArD.then(ArD.then(c1, c2), acc), ArD.then(c1, ArD.then(c2, acc)), ac.then_assoc(c1, c2, acc))
    case +x <> +xr +y <> +yr:
      +Vx = ArT.big.val(xr)
      +Vy = ArT.big.val(yr)
      +c1 = Nat.cmp(Vx, Vy)
      +c2 = Nat.cmp(x, y)
      +rhs = ArD.then(Nat.cmp(Nat.add(x, Nat.mul(Vx, 10n)), Nat.add(y, Nat.mul(Vy, 10n))), acc)
      %Equal.sym(Cmp, ArT.big.cmp(xr, yr, ArD.then(c2, acc)), ArD.then(c1, ArD.then(c2, acc)), ac.cmp_val(xr, yr, ArD.then(c2, acc), ac.dok_tl(x, xr, ha), ac.dok_tl(y, yr, hb))) : {_ == rhs : Cmp}
      %Equal.sym(Cmp, Nat.cmp(Nat.add(x, Nat.mul(Vx, 10n)), Nat.add(y, Nat.mul(Vy, 10n))), ArD.then(c1, c2), ac.cmp_dig(x, y, Vx, Vy, ac.dok_hd(x, xr, ha), ac.dok_hd(y, yr, hb))) : {ArD.then(c1, ArD.then(c2, acc)) == ArD.then(_, acc) : Cmp}
      Equal.sym(Cmp, ArD.then(ArD.then(c1, c2), acc), ArD.then(c1, ArD.then(c2, acc)), ac.then_assoc(c1, c2, acc))

# Differences
# -----------

def ac.add_1(+V: Nat) -> {Nat.add(V, 1n) == 1n+V : Nat}:
  %CN.ac.add_zero(V) : {Nat.add(V, 1n) == 1n+_ : Nat}
  CN.ac.add_succ(V, 0n)

def ac.one_le(b: Bool) -> {Nat.is_le(ArS.one(b), 1n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# 10 + x - k is a digit for x < k
def ac.sub_lt10(x: Nat, k: Nat, h: {Nat.is_lt(x, k) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(Nat.add(10n, x), k), 10n) == True{} : Bool}:
  match x k:
    case x 0n:
      CN.ac.lt0({Nat.is_lt(Nat.sub(Nat.add(10n, x), 0n), 10n) == True{} : Bool}, x, h)
    case 0n 1n++q:
      %CN.ac.le_lt_succ(Nat.sub(9n, q), 9n) : {_ == True{} : Bool}
      CN.ac.sub_le_self(9n, q)
    case 1n++p 1n++q:
      ac.sub_lt10(p, q, h)

def ac.dok_at(low: Bool, +x: Nat, +k: Nat, -rec: List<&2, Nat>, hlow: {Nat.is_lt(x, k) == low : Bool}, hx: {Nat.is_lt(x, 10n) == True{} : Bool}, hr: {SD.digits_ok(rec) == True{} : Bool}) -> {SD.digits_ok(ArT.big.sub.at(low, x, k, rec)) == True{} : Bool}:
  match low:
    case True{}:
      ac.dok_cons(Nat.sub(Nat.add(10n, x), k), rec, ac.sub_lt10(x, k, hlow), hr)
    case False{}:
      ac.dok_cons(Nat.sub(x, k), rec, CN.ac.le_lt_trans(Nat.sub(x, k), x, 10n, CN.ac.sub_le_self(x, k), hx), hr)

# a difference of digit lists is digits
def ac.dok_sub(+a: List<&2, Nat>, +b: List<&2, Nat>, +br: Nat, +ha: {SD.digits_ok(a) == True{} : Bool}) -> {SD.digits_ok(ArT.big.sub(a, b, br)) == True{} : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      {==}
    case +x <> +xr Nil{}:
      +low = Nat.is_lt(x, br)
      ac.dok_at(low, x, br, ArT.big.sub(xr, Nil{}, ArS.one(low)), {==}, ac.dok_hd(x, xr, ha), ac.dok_sub(xr, Nil{}, ArS.one(low), ac.dok_tl(x, xr, ha)))
    case +x <> +xr +y <> +yr:
      +k = Nat.add(y, br)
      +low = Nat.is_lt(x, k)
      ac.dok_at(low, x, k, ArT.big.sub(xr, yr, ArS.one(low)), {==}, ac.dok_hd(x, xr, ha), ac.dok_sub(xr, yr, ArS.one(low), ac.dok_tl(x, xr, ha)))

# k + 10 A <= x + 10 B with x < k: A < B
def ac.mul10_lt(A: Nat, B: Nat, +k: Nat, +x: Nat, +h: {Nat.is_le(Nat.add(k, Nat.mul(A, 10n)), Nat.add(x, Nat.mul(B, 10n))) == True{} : Bool}, +hl: {Nat.is_lt(x, k) == True{} : Bool}) -> {Nat.is_lt(A, B) == True{} : Bool}:
  match A B:
    case 0n 0n:
      +h2 = {%CN.ac.add_zero(k) : {Nat.is_le(_, x) == True{} : Bool}; %CN.ac.add_zero(x) : {Nat.is_le(Nat.add(k, 0n), _) == True{} : Bool}; h : {Nat.is_le(k, x) == True{} : Bool}}
      CN.ac.ft({Nat.is_lt(0n, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(x, k), True{}, Equal.sym(Bool, Nat.is_lt(x, k), False{}, CN.ac.le_not_lt(k, x, h2)), hl))
    case 0n 1n++b:
      {==}
    case 1n++a 0n:
      +W = Nat.add(10n, Nat.mul(a, 10n))
      +h2 = {%CN.ac.add_zero(x) : {Nat.is_le(Nat.add(k, W), _) == True{} : Bool}; h : {Nat.is_le(Nat.add(k, W), x) == True{} : Bool}}
      +h3 = CN.ac.le_trans(k, Nat.add(k, W), x, CN.ac.le_add(k, W), h2)
      CN.ac.ft({Nat.is_lt(1n+a, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(x, k), True{}, Equal.sym(Bool, Nat.is_lt(x, k), False{}, CN.ac.le_not_lt(k, x, h3)), hl))
    case 1n++a 1n++b:
      +Ma = Nat.mul(a, 10n)
      +Mb = Nat.mul(b, 10n)
      +h2 = {%Equal.sym(Nat, Nat.add(10n, Nat.add(k, Ma)), Nat.add(k, Nat.add(10n, Ma)), CN.ac.add_swap(10n, k, Ma)) : {Nat.is_le(_, Nat.add(10n, Nat.add(x, Mb))) == True{} : Bool}; %Equal.sym(Nat, Nat.add(10n, Nat.add(x, Mb)), Nat.add(x, Nat.add(10n, Mb)), CN.ac.add_swap(10n, x, Mb)) : {Nat.is_le(Nat.add(k, Nat.add(10n, Ma)), _) == True{} : Bool}; h : {Nat.is_le(Nat.add(10n, Nat.add(k, Ma)), Nat.add(10n, Nat.add(x, Mb))) == True{} : Bool}}
      ac.mul10_lt(a, b, k, x, h2, hl)

# k + 10 A <= x + 10 B with x a digit: A <= B
def ac.mul10_le(A: Nat, B: Nat, +k: Nat, +x: Nat, +h: {Nat.is_le(Nat.add(k, Nat.mul(A, 10n)), Nat.add(x, Nat.mul(B, 10n))) == True{} : Bool}, +hx: {Nat.is_lt(x, 10n) == True{} : Bool}) -> {Nat.is_le(A, B) == True{} : Bool}:
  match A B:
    case 0n bb:
      CN.ac.le_zero(bb)
    case 1n++a 0n:
      +W = Nat.add(k, Nat.mul(a, 10n))
      +h2 = {%CN.ac.add_zero(x) : {Nat.is_le(Nat.add(10n, W), _) == True{} : Bool}; %Equal.sym(Nat, Nat.add(10n, W), Nat.add(k, Nat.add(10n, Nat.mul(a, 10n))), CN.ac.add_swap(10n, k, Nat.mul(a, 10n))) : {Nat.is_le(_, Nat.add(x, 0n)) == True{} : Bool}; h : {Nat.is_le(Nat.add(10n, W), x) == True{} : Bool}}
      +h3 = CN.ac.le_trans(10n, Nat.add(10n, W), x, CN.ac.le_add(10n, W), h2)
      CN.ac.ft({Nat.is_le(1n+a, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(x, 10n), True{}, Equal.sym(Bool, Nat.is_lt(x, 10n), False{}, CN.ac.le_not_lt(10n, x, h3)), hx))
    case 1n++a 1n++b:
      +Ma = Nat.mul(a, 10n)
      +Mb = Nat.mul(b, 10n)
      +h2 = {%Equal.sym(Nat, Nat.add(10n, Nat.add(k, Ma)), Nat.add(k, Nat.add(10n, Ma)), CN.ac.add_swap(10n, k, Ma)) : {Nat.is_le(_, Nat.add(10n, Nat.add(x, Mb))) == True{} : Bool}; %Equal.sym(Nat, Nat.add(10n, Nat.add(x, Mb)), Nat.add(x, Nat.add(10n, Mb)), CN.ac.add_swap(10n, x, Mb)) : {Nat.is_le(Nat.add(k, Nat.add(10n, Ma)), _) == True{} : Bool}; h : {Nat.is_le(Nat.add(10n, Nat.add(k, Ma)), Nat.add(10n, Nat.add(x, Mb))) == True{} : Bool}}
      ac.mul10_le(a, b, k, x, h2, hx)

# the borrow taken from the rest is affordable
def ac.sub_pre(low: Bool, +x: Nat, +k: Nat, +Vyr: Nat, +Vxr: Nat, +hlow: {Nat.is_lt(x, k) == low : Bool}, +hx: {Nat.is_lt(x, 10n) == True{} : Bool}, +h: {Nat.is_le(Nat.add(k, Nat.mul(Vyr, 10n)), Nat.add(x, Nat.mul(Vxr, 10n))) == True{} : Bool}) -> {Nat.is_le(Nat.add(Vyr, ArS.one(low)), Vxr) == True{} : Bool}:
  match low:
    case True{}:
      %Equal.sym(Nat, Nat.add(Vyr, 1n), 1n+Vyr, ac.add_1(Vyr)) : {Nat.is_le(_, Vxr) == True{} : Bool}
      %CN.ac.lt_le_succ(Vyr, Vxr) : {_ == True{} : Bool}
      ac.mul10_lt(Vyr, Vxr, k, x, h, hlow)
    case False{}:
      %Equal.sym(Nat, Nat.add(Vyr, 0n), Vyr, CN.ac.add_zero(Vyr)) : {Nat.is_le(_, Vxr) == True{} : Bool}
      ac.mul10_le(Vyr, Vxr, k, x, h, hx)

# one digit of a difference and the difference of the rest
def ac.sub_at_val(low: Bool, +x: Nat, +k: Nat, +rec: List<&2, Nat>, +Vyr: Nat, +Vxr: Nat, +hlow: {Nat.is_lt(x, k) == low : Bool}, +hk: {Nat.is_le(k, 10n) == True{} : Bool}, +ih: {Nat.add(ArT.big.val(rec), Nat.add(Vyr, ArS.one(low))) == Vxr : Nat}) -> {Nat.add(ArT.big.val(ArT.big.sub.at(low, x, k, rec)), Nat.add(k, Nat.mul(Vyr, 10n))) == Nat.add(x, Nat.mul(Vxr, 10n)) : Nat}:
  match low:
    case True{}:
      +R = ArT.big.val(rec)
      +MR = Nat.mul(R, 10n)
      +MV = Nat.mul(Vyr, 10n)
      +M = Nat.mul(Nat.add(R, Vyr), 10n)
      +d = Nat.sub(Nat.add(10n, x), k)
      +hle = CN.ac.le_trans(k, 10n, Nat.add(10n, x), hk, CN.ac.le_add(10n, x))
      +e1 = Equal.trans(Nat, Nat.add(d, k), Nat.add(k, d), Nat.add(10n, x), CN.ac.add_comm(d, k), CN.ac.add_sub(k, Nat.add(10n, x), hle))
      +lhs = Nat.add(Nat.add(d, MR), Nat.add(k, MV))
      %ih : {lhs == Nat.add(x, Nat.mul(_, 10n)) : Nat}
      %Equal.sym(Nat, Nat.add(R, Nat.add(Vyr, 1n)), 1n+Nat.add(R, Vyr), {%Equal.sym(Nat, Nat.add(Vyr, 1n), 1n+Vyr, ac.add_1(Vyr)) : {Nat.add(R, _) == 1n+Nat.add(R, Vyr) : Nat}; CN.ac.add_succ(R, Vyr) : {Nat.add(R, Nat.add(Vyr, 1n)) == 1n+Nat.add(R, Vyr) : Nat}}) : {lhs == Nat.add(x, Nat.mul(_, 10n)) : Nat}
      %Equal.sym(Nat, lhs, Nat.add(Nat.add(d, k), Nat.add(MR, MV)), CN.ac.add_4(d, MR, k, MV)) : {_ == Nat.add(x, Nat.add(10n, M)) : Nat}
      %Equal.sym(Nat, Nat.add(d, k), Nat.add(10n, x), e1) : {Nat.add(_, Nat.add(MR, MV)) == Nat.add(x, Nat.add(10n, M)) : Nat}
      %CN.ac.mul_add(R, Vyr, 10n) : {Nat.add(Nat.add(10n, x), _) == Nat.add(x, Nat.add(10n, M)) : Nat}
      %CN.ac.add_swap(10n, x, M) : {Nat.add(Nat.add(10n, x), M) == _ : Nat}
      CN.ac.add_assoc(10n, x, M)
    case False{}:
      +R = ArT.big.val(rec)
      +MR = Nat.mul(R, 10n)
      +MV = Nat.mul(Vyr, 10n)
      +M = Nat.mul(Nat.add(R, Vyr), 10n)
      +d = Nat.sub(x, k)
      +hkx = CN.ac.le_of_not_lt(x, k, hlow)
      +e1 = Equal.trans(Nat, Nat.add(d, k), Nat.add(k, d), x, CN.ac.add_comm(d, k), CN.ac.add_sub(k, x, hkx))
      +lhs = Nat.add(Nat.add(d, MR), Nat.add(k, MV))
      %ih : {lhs == Nat.add(x, Nat.mul(_, 10n)) : Nat}
      %Equal.sym(Nat, Nat.add(Vyr, 0n), Vyr, CN.ac.add_zero(Vyr)) : {lhs == Nat.add(x, Nat.mul(Nat.add(R, _), 10n)) : Nat}
      %Equal.sym(Nat, lhs, Nat.add(Nat.add(d, k), Nat.add(MR, MV)), CN.ac.add_4(d, MR, k, MV)) : {_ == Nat.add(x, M) : Nat}
      %Equal.sym(Nat, Nat.add(d, k), x, e1) : {Nat.add(_, Nat.add(MR, MV)) == Nat.add(x, M) : Nat}
      %CN.ac.mul_add(R, Vyr, 10n) : {Nat.add(x, _) == Nat.add(x, M) : Nat}
      {==}

# big.sub is a - b - borrow, for a >= b + borrow
def ac.val_sub(+a: List<&2, Nat>, +b: List<&2, Nat>, +br: Nat, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}, +hbr: {Nat.is_le(br, 1n) == True{} : Bool}, +h: {Nat.is_le(Nat.add(ArT.big.val(b), br), ArT.big.val(a)) == True{} : Bool}) -> {Nat.add(ArT.big.val(ArT.big.sub(a, b, br)), Nat.add(ArT.big.val(b), br)) == ArT.big.val(a) : Nat}:
  match a b:
    case Nil{} Nil{}:
      CN.ac.le0_eq(br, h)
    case Nil{} +y <> +yr:
      CN.ac.le0_eq(Nat.add(Nat.add(y, Nat.mul(ArT.big.val(yr), 10n)), br), h)
    case +x <> +xr Nil{}:
      +low = Nat.is_lt(x, br)
      +Vxr = ArT.big.val(xr)
      +rec = ArT.big.sub(xr, Nil{}, ArS.one(low))
      +hx = ac.dok_hd(x, xr, ha)
      +h2 = {%Equal.sym(Nat, Nat.add(br, 0n), br, CN.ac.add_zero(br)) : {Nat.is_le(_, Nat.add(x, Nat.mul(Vxr, 10n))) == True{} : Bool}; h : {Nat.is_le(Nat.add(br, 0n), Nat.add(x, Nat.mul(Vxr, 10n))) == True{} : Bool}}
      +pre = ac.sub_pre(low, x, br, 0n, Vxr, {==}, hx, h2)
      +ih = ac.val_sub(xr, Nil{}, ArS.one(low), ac.dok_tl(x, xr, ha), hb, ac.one_le(low), pre)
      +hk = CN.ac.le_trans(br, 1n, 10n, hbr, {==})
      +st = ac.sub_at_val(low, x, br, rec, 0n, Vxr, {==}, hk, ih)
      %CN.ac.add_zero(br) : {Nat.add(ArT.big.val(ArT.big.sub.at(low, x, br, rec)), _) == Nat.add(x, Nat.mul(Vxr, 10n)) : Nat}
      st
    case +x <> +xr +y <> +yr:
      +k = Nat.add(y, br)
      +low = Nat.is_lt(x, k)
      +Vxr = ArT.big.val(xr)
      +Vyr = ArT.big.val(yr)
      +MV = Nat.mul(Vyr, 10n)
      +rec = ArT.big.sub(xr, yr, ArS.one(low))
      +hx = ac.dok_hd(x, xr, ha)
      +h2 = {%CN.ac.add_rcomm(y, MV, br) : {Nat.is_le(_, Nat.add(x, Nat.mul(Vxr, 10n))) == True{} : Bool}; h : {Nat.is_le(Nat.add(k, MV), Nat.add(x, Nat.mul(Vxr, 10n))) == True{} : Bool}}
      +pre = ac.sub_pre(low, x, k, Vyr, Vxr, {==}, hx, h2)
      +ih = ac.val_sub(xr, yr, ArS.one(low), ac.dok_tl(x, xr, ha), ac.dok_tl(y, yr, hb), ac.one_le(low), pre)
      +hk = CN.ac.le_add_mono(y, 9n, br, 1n, ac.lt10_le9(y, ac.dok_hd(y, yr, hb)), hbr)
      +st = ac.sub_at_val(low, x, k, rec, Vyr, Vxr, {==}, hk, ih)
      %CN.ac.add_rcomm(y, br, MV) : {Nat.add(ArT.big.val(ArT.big.sub.at(low, x, k, rec)), _) == Nat.add(x, Nat.mul(Vxr, 10n)) : Nat}
      st

# |a - b| as the spec writes it: (a - b) + (b - a)
def ac.dist(+a: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.sub(a, b), Nat.sub(b, a))

# a below b: big.sub(b, a, 0) is b - a
def ac.diff_lt(+a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}, +hlt: {Nat.is_lt(ArT.big.val(a), ArT.big.val(b)) == True{} : Bool}) -> {ArT.big.val(ArT.big.sub(b, a, 0n)) == ac.dist(ArT.big.val(a), ArT.big.val(b)) : Nat}:
  +va = ArT.big.val(a)
  +vb = ArT.big.val(b)
  +V = ArT.big.val(ArT.big.sub(b, a, 0n))
  +hle = CN.ac.lt_le(va, vb, hlt)
  +hle0 = {%Equal.sym(Nat, Nat.add(va, 0n), va, CN.ac.add_zero(va)) : {Nat.is_le(_, vb) == True{} : Bool}; hle : {Nat.is_le(Nat.add(va, 0n), vb) == True{} : Bool}}
  +vs = ac.val_sub(b, a, 0n, hb, ha, {==}, hle0)
  %Equal.sym(Nat, Nat.sub(va, vb), 0n, CN.ac.sub_le(va, vb, hle)) : {V == Nat.add(_, Nat.sub(vb, va)) : Nat}
  %Equal.cong(Nat, Nat, t => Nat.sub(vb, t), Nat.add(va, 0n), va, CN.ac.add_zero(va)) : {V == _ : Nat}
  Equal.sym(Nat, Nat.sub(vb, Nat.add(va, 0n)), V, CN.ac.sub_of_sum(V, Nat.add(va, 0n), vb, vs))

# a not below b: big.sub(a, b, 0) is a - b
def ac.diff_ge(+a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}, +hnl: {Nat.is_lt(ArT.big.val(a), ArT.big.val(b)) == False{} : Bool}) -> {ArT.big.val(ArT.big.sub(a, b, 0n)) == ac.dist(ArT.big.val(a), ArT.big.val(b)) : Nat}:
  +va = ArT.big.val(a)
  +vb = ArT.big.val(b)
  +V = ArT.big.val(ArT.big.sub(a, b, 0n))
  +hle = CN.ac.le_of_not_lt(va, vb, hnl)
  +hle0 = {%Equal.sym(Nat, Nat.add(vb, 0n), vb, CN.ac.add_zero(vb)) : {Nat.is_le(_, va) == True{} : Bool}; hle : {Nat.is_le(Nat.add(vb, 0n), va) == True{} : Bool}}
  +vs = ac.val_sub(a, b, 0n, ha, hb, {==}, hle0)
  %Equal.sym(Nat, Nat.sub(vb, va), 0n, CN.ac.sub_le(vb, va, hle)) : {V == Nat.add(Nat.sub(va, vb), _) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.sub(va, vb), 0n), Nat.sub(va, vb), CN.ac.add_zero(Nat.sub(va, vb))) : {V == _ : Nat}
  %Equal.cong(Nat, Nat, t => Nat.sub(va, t), Nat.add(vb, 0n), vb, CN.ac.add_zero(vb)) : {V == _ : Nat}
  Equal.sym(Nat, Nat.sub(va, Nat.add(vb, 0n)), V, CN.ac.sub_of_sum(V, Nat.add(vb, 0n), va, vs))

def ac.diff_at(c: Cmp, +a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}, +e: {Nat.cmp(ArT.big.val(a), ArT.big.val(b)) == c : Cmp}) -> {ArT.big.val(ArT.big.diff.at(c, a, b)) == ac.dist(ArT.big.val(a), ArT.big.val(b)) : Nat}:
  match c:
    case LT{}:
      ac.diff_lt(a, b, ha, hb, {%Equal.sym(Cmp, Nat.cmp(ArT.big.val(a), ArT.big.val(b)), LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}; {==} : {Nat.is_lt(ArT.big.val(a), ArT.big.val(b)) == True{} : Bool}})
    case EQ{}:
      ac.diff_ge(a, b, ha, hb, {%Equal.sym(Cmp, Nat.cmp(ArT.big.val(a), ArT.big.val(b)), EQ{}, e) : {Cmp.is_lt(_) == False{} : Bool}; {==} : {Nat.is_lt(ArT.big.val(a), ArT.big.val(b)) == False{} : Bool}})
    case GT{}:
      ac.diff_ge(a, b, ha, hb, {%Equal.sym(Cmp, Nat.cmp(ArT.big.val(a), ArT.big.val(b)), GT{}, e) : {Cmp.is_lt(_) == False{} : Bool}; {==} : {Nat.is_lt(ArT.big.val(a), ArT.big.val(b)) == False{} : Bool}})

# big.diff is |a - b|
def ac.val_diff(+a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}) -> {ArT.big.val(ArT.big.diff(a, b)) == ac.dist(ArT.big.val(a), ArT.big.val(b)) : Nat}:
  +c = Nat.cmp(ArT.big.val(a), ArT.big.val(b))
  +e = Equal.trans(Cmp, c, ArD.then(c, EQ{}), ArT.big.cmp(a, b, EQ{}), Equal.sym(Cmp, ArD.then(c, EQ{}), c, ac.then_eq(c)), Equal.sym(Cmp, ArT.big.cmp(a, b, EQ{}), ArD.then(c, EQ{}), ac.cmp_val(a, b, EQ{}, ha, hb)))
  %e : {ArT.big.val(ArT.big.diff.at(_, a, b)) == ac.dist(ArT.big.val(a), ArT.big.val(b)) : Nat}
  ac.diff_at(c, a, b, ha, hb, {==})

def ac.dok_diff_at(c: Cmp, +a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}) -> {SD.digits_ok(ArT.big.diff.at(c, a, b)) == True{} : Bool}:
  match c:
    case LT{}:
      ac.dok_sub(b, a, 0n, hb)
    case EQ{}:
      ac.dok_sub(a, b, 0n, ha)
    case GT{}:
      ac.dok_sub(a, b, 0n, ha)

def ac.dok_diff(+a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}) -> {SD.digits_ok(ArT.big.diff(a, b)) == True{} : Bool}:
  ac.dok_diff_at(ArT.big.cmp(a, b, EQ{}), a, b, ha, hb)

# Zero
# ----

def ac.mul10_eq0(V: Nat) -> {Nat.is_eq(Nat.mul(V, 10n), 0n) == Nat.is_eq(V, 0n) : Bool}:
  match V:
    case 0n:
      {==}
    case 1n++v:
      {==}

# big.zero is a value of 0
def ac.zero_val(xs: List<&2, Nat>) -> {ArT.big.zero(xs) == Nat.is_eq(ArT.big.val(xs), 0n) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case 0n:
          Equal.trans(Bool, Bool.not(ArD.nz(t)), Nat.is_eq(ArT.big.val(t), 0n), Nat.is_eq(Nat.mul(ArT.big.val(t), 10n), 0n), ac.zero_val(t), Equal.sym(Bool, Nat.is_eq(Nat.mul(ArT.big.val(t), 10n), 0n), Nat.is_eq(ArT.big.val(t), 0n), ac.mul10_eq0(ArT.big.val(t))))
        case 1n++p:
          {==}

# Reversed decimal digits
# -----------------------

def ac.val_rev(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {ArT.big.val(ArT.rev(xs, acc)) == SD.num.go(xs, ArT.big.val(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +M = Nat.mul(ArT.big.val(acc), 10n)
      %CN.ac.add_comm(x, M) : {ArT.big.val(ArT.rev(t, x <> acc)) == SD.num.go(t, _) : Nat}
      ac.val_rev(t, x <> acc)

def ac.num_cat(xs: List<&2, Nat>, +ys: List<&2, Nat>, +a: Nat) -> {SD.num.go(ArD.cat(xs, ys), a) == SD.num.go(ys, SD.num.go(xs, a)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      ac.num_cat(t, ys, Nat.add(Nat.mul(a, 10n), x))

def ac.num_zeros(k: Nat, +a: Nat) -> {SD.num.go(ArD.zeros(k), a) == SD.shift(k, a) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(Nat.mul(a, 10n), 0n), Nat.mul(a, 10n), CN.ac.add_zero(Nat.mul(a, 10n))) : {SD.num.go(ArD.zeros(p), _) == SD.shift(p, Nat.mul(a, 10n)) : Nat}
      ac.num_zeros(p, Nat.mul(a, 10n))

# a decimal's magnitude at scale sc is worth its digits shifted by sc - s
def ac.val_mag(d: ArD.Dec, +sc: Nat) -> {ArT.big.val(ArT.mag(d, sc)) == SD.shift(Nat.sub(sc, ArT.scale(d)), SD.num(ArD.Dec.ds(d))) : Nat}:
  match d:
    case ArD.Dec{neg, +ds, +s}:
      +k = Nat.sub(sc, s)
      %Equal.sym(Nat, ArT.big.val(ArT.rev(ArD.cat(ds, ArD.zeros(k)), Nil{})), SD.num.go(ArD.cat(ds, ArD.zeros(k)), 0n), ac.val_rev(ArD.cat(ds, ArD.zeros(k)), Nil{})) : {_ == SD.shift(k, SD.num(ds)) : Nat}
      %Equal.sym(Nat, SD.num.go(ArD.cat(ds, ArD.zeros(k)), 0n), SD.num.go(ArD.zeros(k), SD.num.go(ds, 0n)), ac.num_cat(ds, ArD.zeros(k), 0n)) : {_ == SD.shift(k, SD.num(ds)) : Nat}
      ac.num_zeros(k, SD.num.go(ds, 0n))

def ac.dok_cat(xs: List<&2, Nat>, -ys: List<&2, Nat>, +hx: {SD.digits_ok(xs) == True{} : Bool}, hy: {SD.digits_ok(ys) == True{} : Bool}) -> {SD.digits_ok(ArD.cat(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +t:
      ac.dok_cons(x, ArD.cat(t, ys), ac.dok_hd(x, t, hx), ac.dok_cat(t, ys, ac.dok_tl(x, t, hx), hy))

def ac.dok_zeros(k: Nat) -> {SD.digits_ok(ArD.zeros(k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      ac.dok_zeros(p)

def ac.dok_rev(xs: List<&2, Nat>, +acc: List<&2, Nat>, +hx: {SD.digits_ok(xs) == True{} : Bool}, +ha: {SD.digits_ok(acc) == True{} : Bool}) -> {SD.digits_ok(ArT.rev(xs, acc)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case +x <> +t:
      ac.dok_rev(t, x <> acc, ac.dok_tl(x, t, hx), ac.dok_cons(x, acc, ac.dok_hd(x, t, hx), ha))

def ac.dok_mag(d: ArD.Dec, +sc: Nat, +w: {SD.Wf(d) == True{} : Bool}) -> {SD.digits_ok(ArT.mag(d, sc)) == True{} : Bool}:
  match d:
    case ArD.Dec{neg, +ds, +s}:
      ac.dok_rev(ArD.cat(ds, ArD.zeros(Nat.sub(sc, s))), Nil{}, ac.dok_cat(ds, ArD.zeros(Nat.sub(sc, s)), w, ac.dok_zeros(Nat.sub(sc, s))), {==})
