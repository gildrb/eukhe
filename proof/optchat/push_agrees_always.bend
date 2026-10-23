# eukhe: the proof of LAW push_agrees_always

import Base
import ../../bend/optchat.bend as O
import ../../laws/optchat.bend as Optchat
import ../base.bend as L
import ./base.bend as LA

def pa.add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      L.pa.succ(Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), pa.add_assoc(p, b, c))

def pa.double_add(a: Nat, +b: Nat) -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      L.pa.succ(1n+Nat.double(Nat.add(p, b)), 1n+Nat.add(Nat.double(p), Nat.double(b)), L.pa.succ(Nat.double(Nat.add(p, b)), Nat.add(Nat.double(p), Nat.double(b)), pa.double_add(p, b)))

# b + 1 + k is above b
def pa.gt_add(b: Nat, -k: Nat) -> {Nat.is_gt(Nat.add(b, 1n+k), b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      pa.gt_add(p, k)

def pa.gt_succ(n: Nat) -> {Nat.is_gt(1n+n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pa.gt_succ(p)

def pa.gt_self(n: Nat) -> {Nat.is_gt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pa.gt_self(p)

def pa.cmp_self(n: Nat) -> {Nat.cmp(n, n) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pa.cmp_self(p)

# x·2^l, doubling outside
def pa.sh(l: Nat, x: Nat) -> Nat:
  match l:
    case 0n:
      x
    case 1n+p:
      Nat.double(pa.sh(p, x))

def pa.sh_zero(l: Nat) -> {pa.sh(l, 0n) == 0n : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, pa.sh(p, 0n), 0n, pa.sh_zero(p)) : {Nat.double(_) == 0n : Nat}
      {==}

def pa.sh_add(+l: Nat, +a: Nat, +b: Nat) -> {pa.sh(l, Nat.add(a, b)) == Nat.add(pa.sh(l, a), pa.sh(l, b)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.double(pa.sh(p, Nat.add(a, b))), Nat.double(Nat.add(pa.sh(p, a), pa.sh(p, b))), Nat.add(Nat.double(pa.sh(p, a)), Nat.double(pa.sh(p, b))), Equal.cong(Nat, Nat, x => Nat.double(x), pa.sh(p, Nat.add(a, b)), Nat.add(pa.sh(p, a), pa.sh(p, b)), pa.sh_add(p, a, b)), pa.double_add(pa.sh(p, a), pa.sh(p, b)))

def pa.sh_double(+l: Nat, +x: Nat) -> {pa.sh(l, Nat.double(x)) == Nat.double(pa.sh(l, x)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, y => Nat.double(y), pa.sh(p, Nat.double(x)), Nat.double(pa.sh(p, x)), pa.sh_double(p, x))

# Bits and their values
# ---------------------

def pa.val_inc(x: List<&2, Bool>) -> {O.Bits.val(O.Bits.inc(x)) == 1n+O.Bits.val(x) : Nat}:
  match x:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case False{}:
          {==}
        case True{}:
          Equal.cong(Nat, Nat, z => Nat.double(z), O.Bits.val(O.Bits.inc(t)), 1n+O.Bits.val(t), pa.val_inc(t))

def pa.val_shl(l: Nat, +x: List<&2, Bool>) -> {O.Bits.val(O.Bits.shl(l, x)) == pa.sh(l, O.Bits.val(x)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => Nat.double(z), O.Bits.val(O.Bits.shl(p, x)), pa.sh(p, O.Bits.val(x)), pa.val_shl(p, x))

def pa.add_bits(x: Bool, y: Bool, +P: Nat, +Q: Nat) -> {Nat.add(O.bit(x, P), O.bit(y, Q)) == O.bit(x, O.bit(y, Nat.add(P, Q))) : Nat}:
  match x y:
    case False{} False{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      L.pa.add_succ(P, Q)
    case True{} True{}:
      L.pa.succ(Nat.add(P, 1n+Q), 1n+Nat.add(P, Q), L.pa.add_succ(P, Q))

# a full adder: the sum bit, then twice the carry
def pa.fa(x: Bool, y: Bool, c: Bool, -S: Nat) -> {O.bit(Bool.xor(Bool.xor(x, y), c), Nat.double(O.bit(Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))), S))) == O.bit(c, O.bit(x, O.bit(y, Nat.double(S)))) : Nat}:
  match x y c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def pa.val_add.cons(+x: Bool, +y: Bool, +c: Bool, +A: Nat, +B: Nat, -L: Nat,
  ih: {L == O.bit(Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))), Nat.add(A, B)) : Nat})
  -> {O.bit(Bool.xor(Bool.xor(x, y), c), Nat.double(L)) == O.bit(c, Nat.add(O.bit(x, Nat.double(A)), O.bit(y, Nat.double(B)))) : Nat}:
  %Equal.sym(Nat, L, O.bit(Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))), Nat.add(A, B)), ih) : {O.bit(Bool.xor(Bool.xor(x, y), c), Nat.double(_)) == O.bit(c, Nat.add(O.bit(x, Nat.double(A)), O.bit(y, Nat.double(B)))) : Nat}
  %Equal.sym(Nat, Nat.add(O.bit(x, Nat.double(A)), O.bit(y, Nat.double(B))), O.bit(x, O.bit(y, Nat.add(Nat.double(A), Nat.double(B)))), pa.add_bits(x, y, Nat.double(A), Nat.double(B))) : {O.bit(Bool.xor(Bool.xor(x, y), c), Nat.double(O.bit(Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))), Nat.add(A, B)))) == O.bit(c, _) : Nat}
  %pa.double_add(A, B) : {O.bit(Bool.xor(Bool.xor(x, y), c), Nat.double(O.bit(Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))), Nat.add(A, B)))) == O.bit(c, O.bit(x, O.bit(y, _))) : Nat}
  pa.fa(x, y, c, Nat.add(A, B))

# the value of x + y + c
def pa.val_add(xs: List<&2, Bool>, ys: List<&2, Bool>, +c: Bool) -> {O.Bits.val(O.Bits.add.go(xs, ys, c)) == O.bit(c, Nat.add(O.Bits.val(xs), O.Bits.val(ys))) : Nat}:
  match xs ys:
    case Nil{} +ys:
      match c:
        case False{}:
          {==}
        case True{}:
          pa.val_inc(ys)
    case +x <> +xt Nil{}:
      match c:
        case False{}:
          Equal.sym(Nat, Nat.add(O.Bits.val(x <> xt), 0n), O.Bits.val(x <> xt), L.pa.add_zero(O.Bits.val(x <> xt)))
        case True{}:
          Equal.trans(Nat, O.Bits.val(O.Bits.inc(x <> xt)), 1n+O.Bits.val(x <> xt), 1n+Nat.add(O.Bits.val(x <> xt), 0n), pa.val_inc(x <> xt), L.pa.succ(O.Bits.val(x <> xt), Nat.add(O.Bits.val(x <> xt), 0n), Equal.sym(Nat, Nat.add(O.Bits.val(x <> xt), 0n), O.Bits.val(x <> xt), L.pa.add_zero(O.Bits.val(x <> xt)))))
    case +x <> +xt +y <> +yt:
      pa.val_add.cons(x, y, c, O.Bits.val(xt), O.Bits.val(yt), O.Bits.val(O.Bits.add.go(xt, yt, Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))))), pa.val_add(xt, yt, Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y)))))

def pa.gt_val(+xs: List<&2, Bool>, +ys: List<&2, Bool>, e: {Nat.is_gt(O.Bits.val(xs), O.Bits.val(ys)) == True{} : Bool}) -> {O.Bits.gt(xs, ys) == True{} : Bool}:
  %Equal.sym(Cmp, O.Bits.cmp(xs, ys), Nat.cmp(O.Bits.val(xs), O.Bits.val(ys)), LA.pa.cmp_val(xs, ys)) : {Cmp.is_gt(_) == True{} : Bool}
  e

def pa.same_val(+xs: List<&2, Bool>, +ys: List<&2, Bool>, e: {O.Bits.val(xs) == O.Bits.val(ys) : Nat}) -> {O.Bits.same(xs, ys) == True{} : Bool}:
  %Equal.sym(Cmp, O.Bits.cmp(xs, ys), Nat.cmp(O.Bits.val(xs), O.Bits.val(ys)), LA.pa.cmp_val(xs, ys)) : {Cmp.is_eq(_) == True{} : Bool}
  %e : {Cmp.is_eq(Nat.cmp(O.Bits.val(xs), _)) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(O.Bits.val(xs), O.Bits.val(xs)), EQ{}, pa.cmp_self(O.Bits.val(xs))) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# A number's bits
# ---------------
# nb(n): n in binary without high zero bits, as Bits.inc counts

def pa.nb(n: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      O.Bits.inc(pa.nb(p))

def pa.val_nb(+n: Nat) -> {O.Bits.val(pa.nb(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, O.Bits.val(O.Bits.inc(pa.nb(p))), 1n+O.Bits.val(pa.nb(p)), 1n+p, pa.val_inc(pa.nb(p)), L.pa.succ(O.Bits.val(pa.nb(p)), p, pa.val_nb(p)))

def pa.nb_odd(+r: Nat) -> {pa.nb(1n+Nat.double(r)) == True{} <> pa.nb(r) : List<&2, Bool>}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, z => O.Bits.inc(O.Bits.inc(z)), pa.nb(1n+Nat.double(p)), True{} <> pa.nb(p), pa.nb_odd(p))

def pa.nb_even(+p: Nat) -> {pa.nb(2n+Nat.double(p)) == False{} <> pa.nb(1n+p) : List<&2, Bool>}:
  Equal.cong(List<&2, Bool>, List<&2, Bool>, z => O.Bits.inc(z), pa.nb(1n+Nat.double(p)), True{} <> pa.nb(p), pa.nb_odd(p))

def pa.low_even(+r: Nat) -> {O.Bits.low(pa.nb(Nat.double(r))) == False{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, Bool>, pa.nb(2n+Nat.double(p)), False{} <> pa.nb(1n+p), pa.nb_even(p)) : {O.Bits.low(_) == False{} : Bool}
      {==}

def pa.up_even(+r: Nat) -> {O.Bits.up(pa.nb(Nat.double(r))) == pa.nb(r) : List<&2, Bool>}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, Bool>, pa.nb(2n+Nat.double(p)), False{} <> pa.nb(1n+p), pa.nb_even(p)) : {O.Bits.up(_) == pa.nb(1n+p) : List<&2, Bool>}
      {==}

def pa.bits_eq_self(x: List<&2, Bool>) -> {O.Bits.eq(x, x) == True{} : Bool}:
  match x:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case False{}:
          pa.bits_eq_self(t)
        case True{}:
          pa.bits_eq_self(t)

# The counter
# -----------
# ds: push's keep bits, lowest (newest entry) first; T = B(ds) messages.

def pa.B(ds: List<&2, Bool>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case d <> r:
      match d:
        case False{}:
          1n+Nat.double(pa.B(r))
        case True{}:
          2n+Nat.double(pa.B(r))

# one more message: a 0 absorbs, a 1 carries
def pa.inc(ds: List<&2, Bool>) -> List<&2, Bool>:
  match ds:
    case Nil{}:
      [False{}]
    case d <> r:
      match d:
        case False{}:
          True{} <> r
        case True{}:
          False{} <> pa.inc(r)

def pa.B_inc(ds: List<&2, Bool>) -> {pa.B(pa.inc(ds)) == 1n+pa.B(ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          {==}
        case True{}:
          Equal.cong(Nat, Nat, z => 1n+Nat.double(z), pa.B(pa.inc(r)), 1n+pa.B(r), pa.B_inc(r))

# push's list (newest first) at offset j: entry j keeps its digit and
# holds the state where its line starts, sum over k > j of (1 + d_k)·2^k
def pa.GE(ds: List<&2, Bool>, +j: Nat) -> List<&2, O.Entry>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> +r:
      match d:
        case False{}:
          O.Entry{0n, 0n, pa.nb(pa.sh(1n+j, pa.B(r)))} <> pa.GE(r, 1n+j)
        case True{}:
          O.Entry{1n, 0n, pa.nb(pa.sh(1n+j, pa.B(r)))} <> pa.GE(r, 1n+j)

# the view (oldest first): the view of the higher digits one level up,
# then the line of digit 0, of level d_0
def pa.lift(n: O.Node) -> O.Node:
  match n:
    case O.Node{l, i}:
      O.Node{1n+l, i}

def pa.lifts(v: List<&2, O.Node>) -> List<&2, O.Node>:
  match v:
    case Nil{}:
      Nil{}
    case h <> t:
      pa.lift(h) <> pa.lifts(t)

def pa.line(d: Bool, +r: Nat) -> O.Node:
  match d:
    case False{}:
      O.Node{0n, pa.nb(Nat.double(r))}
    case True{}:
      O.Node{1n, pa.nb(r)}

def pa.GV(ds: List<&2, Bool>) -> List<&2, O.Node>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> +r:
      List.append(&2, O.Node, pa.lifts(pa.GV(r)), [pa.line(d, pa.B(r))])

# Push is the counter
# -------------------

def pa.push_ge(ds: List<&2, Bool>, +j: Nat) -> {O.push(pa.GE(ds, j), pa.nb(pa.sh(j, pa.B(ds)))) == pa.GE(pa.inc(ds), j) : List<&2, O.Entry>}:
  match ds:
    case Nil{}:
      %Equal.sym(Nat, pa.sh(j, 0n), 0n, pa.sh_zero(j)) : {[O.Entry{0n, 0n, pa.nb(_)}] == [O.Entry{0n, 0n, pa.nb(Nat.double(_))}] : List<&2, O.Entry>}
      {==}
    case d <> +r:
      match d:
        case False{}:
          {==}
        case True{}:
          %pa.push_ge(r, 1n+j) : {O.Entry{0n, 0n, pa.nb(pa.sh(j, 2n+Nat.double(pa.B(r))))} <> O.push(pa.GE(r, 1n+j), pa.nb(pa.sh(1n+j, pa.B(r)))) == O.Entry{0n, 0n, pa.nb(pa.sh(1n+j, pa.B(pa.inc(r))))} <> _ : List<&2, O.Entry>}
          %pa.B_inc(r) : {O.Entry{0n, 0n, pa.nb(pa.sh(j, Nat.double(_)))} <> O.push(pa.GE(r, 1n+j), pa.nb(pa.sh(1n+j, pa.B(r)))) == O.Entry{0n, 0n, pa.nb(pa.sh(1n+j, pa.B(pa.inc(r))))} <> O.push(pa.GE(r, 1n+j), pa.nb(pa.sh(1n+j, pa.B(r)))) : List<&2, O.Entry>}
          %pa.sh_double(j, pa.B(pa.inc(r))) : {O.Entry{0n, 0n, pa.nb(pa.sh(j, Nat.double(pa.B(pa.inc(r)))))} <> O.push(pa.GE(r, 1n+j), pa.nb(pa.sh(1n+j, pa.B(r)))) == O.Entry{0n, 0n, pa.nb(_)} <> O.push(pa.GE(r, 1n+j), pa.nb(pa.sh(1n+j, pa.B(r)))) : List<&2, O.Entry>}
          {==}

# Push's list is the view
# -----------------------
# Compared by value: the view's starts and push's states, oldest first.

def pa.vals(xs: List<&2, List<&2, Bool>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      O.Bits.val(h) <> pa.vals(t)

def pa.dbls(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      Nat.double(h) <> pa.dbls(t)

def pa.hd(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      h

def pa.tl(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

def pa.NilT(xs: List<&2, Nat>, A: Type) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      A

def pa.nil_cons(-A: Type, -h: Nat, -t: List<&2, Nat>, e: {Nil{} == h <> t : List<&2, Nat>}) -> A:
  %e : pa.NilT(_, A)
  Unit{}

def pa.same_vals(xs: List<&2, List<&2, Bool>>, ys: List<&2, List<&2, Bool>>, +e: {pa.vals(xs) == pa.vals(ys) : List<&2, Nat>}) -> {O.Bitss.same(xs, ys) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      pa.nil_cons({False{} == True{} : Bool}, O.Bits.val(y), pa.vals(yt), e)
    case +x <> +xt Nil{}:
      pa.nil_cons({False{} == True{} : Bool}, O.Bits.val(x), pa.vals(xt), Equal.sym(List<&2, Nat>, O.Bits.val(x) <> pa.vals(xt), Nil{}, e))
    case +x <> +xt +y <> +yt:
      %Equal.sym(Bool, O.Bits.same(x, y), True{}, pa.same_val(x, y, Equal.cong(List<&2, Nat>, Nat, z => pa.hd(z), O.Bits.val(x) <> pa.vals(xt), O.Bits.val(y) <> pa.vals(yt), e))) : {Bool.and(_, O.Bitss.same(xt, yt)) == True{} : Bool}
      pa.same_vals(xt, yt, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => pa.tl(z), O.Bits.val(x) <> pa.vals(xt), O.Bits.val(y) <> pa.vals(yt), e))

def pa.vals_rev(xs: List<&2, List<&2, Bool>>, acc: List<&2, List<&2, Bool>>) -> {pa.vals(List.reverse.go(&2, List<&2, Bool>, xs, acc)) == List.reverse.go(&2, Nat, pa.vals(xs), pa.vals(acc)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      pa.vals_rev(t, h <> acc)

def pa.app_assoc(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>) -> {List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) == List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => h <> z, List.append(&2, Nat, List.append(&2, Nat, t, ys), zs), List.append(&2, Nat, t, List.append(&2, Nat, ys, zs)), pa.app_assoc(t, ys, zs))

# reversing onto acc is reversing, then acc
def pa.rev_app(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {List.reverse.go(&2, Nat, xs, acc) == List.append(&2, Nat, List.reverse.go(&2, Nat, xs, Nil{}), acc) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      +R = List.reverse.go(&2, Nat, t, Nil{})
      %Equal.sym(List<&2, Nat>, List.reverse.go(&2, Nat, t, [h]), List.append(&2, Nat, R, [h]), pa.rev_app(t, [h])) : {List.reverse.go(&2, Nat, t, h <> acc) == List.append(&2, Nat, _, acc) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, R, [h]), acc), List.append(&2, Nat, R, h <> acc), pa.app_assoc(R, [h], acc)) : {List.reverse.go(&2, Nat, t, h <> acc) == _ : List<&2, Nat>}
      pa.rev_app(t, h <> acc)

def pa.dbls_rev(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {List.reverse.go(&2, Nat, pa.dbls(xs), pa.dbls(acc)) == pa.dbls(List.reverse.go(&2, Nat, xs, acc)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      pa.dbls_rev(t, h <> acc)

def pa.SG(ds: List<&2, Bool>) -> List<&2, Nat>:
  pa.vals(O.starts(pa.GV(ds)))

def pa.SE(ds: List<&2, Bool>, +j: Nat) -> List<&2, Nat>:
  pa.vals(O.states(pa.GE(ds, j)))

def pa.cons2(-a: Nat, -b: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>, ea: {a == b : Nat}, et: {xs == ys : List<&2, Nat>}) -> {a <> xs == b <> ys : List<&2, Nat>}:
  %ea : {a <> xs == _ <> ys : List<&2, Nat>}
  %et : {a <> xs == a <> _ : List<&2, Nat>}
  {==}

# val(nb(2x)) = 2·val(nb(x))
def pa.val_nb2(+x: Nat) -> {O.Bits.val(pa.nb(Nat.double(x))) == Nat.double(O.Bits.val(pa.nb(x))) : Nat}:
  Equal.trans(Nat, O.Bits.val(pa.nb(Nat.double(x))), Nat.double(x), Nat.double(O.Bits.val(pa.nb(x))), pa.val_nb(Nat.double(x)), Equal.cong(Nat, Nat, z => Nat.double(z), x, O.Bits.val(pa.nb(x)), Equal.sym(Nat, O.Bits.val(pa.nb(x)), x, pa.val_nb(x))))

def pa.vs_app(xs: List<&2, O.Node>, +y: O.Node) -> {pa.vals(O.starts(List.append(&2, O.Node, xs, [y]))) == List.append(&2, Nat, pa.vals(O.starts(xs)), [O.Bits.val(O.pair_start(y))]) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => O.Bits.val(O.pair_start(h)) <> z, pa.vals(O.starts(List.append(&2, O.Node, t, [y]))), List.append(&2, Nat, pa.vals(O.starts(t)), [O.Bits.val(O.pair_start(y))]), pa.vs_app(t, y))

def pa.vs_lifts(xs: List<&2, O.Node>) -> {pa.vals(O.starts(pa.lifts(xs))) == pa.dbls(pa.vals(O.starts(xs))) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case O.Node{+l, +i}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Nat.double(O.Bits.val(O.Bits.shl(l, i))) <> z, pa.vals(O.starts(pa.lifts(t))), pa.dbls(pa.vals(O.starts(t))), pa.vs_lifts(t))

# one level up, every state doubles
def pa.vst(ds: List<&2, Bool>, +j: Nat) -> {pa.SE(ds, 1n+j) == pa.dbls(pa.SE(ds, j)) : List<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          pa.cons2(O.Bits.val(pa.nb(Nat.double(pa.sh(1n+j, pa.B(r))))), Nat.double(O.Bits.val(pa.nb(pa.sh(1n+j, pa.B(r))))), pa.SE(r, 2n+j), pa.dbls(pa.SE(r, 1n+j)), pa.val_nb2(pa.sh(1n+j, pa.B(r))), pa.vst(r, 1n+j))
        case True{}:
          pa.cons2(O.Bits.val(pa.nb(Nat.double(pa.sh(1n+j, pa.B(r))))), Nat.double(O.Bits.val(pa.nb(pa.sh(1n+j, pa.B(r))))), pa.SE(r, 2n+j), pa.dbls(pa.SE(r, 1n+j)), pa.val_nb2(pa.sh(1n+j, pa.B(r))), pa.vst(r, 1n+j))

def pa.rev(xs: List<&2, Nat>) -> List<&2, Nat>:
  List.reverse.go(&2, Nat, xs, Nil{})

def pa.app2(-xs: List<&2, Nat>, -ys: List<&2, Nat>, -a: Nat, -b: Nat, et: {xs == ys : List<&2, Nat>}, ea: {a == b : Nat}) -> {List.append(&2, Nat, xs, [a]) == List.append(&2, Nat, ys, [b]) : List<&2, Nat>}:
  %et : {List.append(&2, Nat, xs, [a]) == List.append(&2, Nat, _, [b]) : List<&2, Nat>}
  %ea : {List.append(&2, Nat, xs, [a]) == List.append(&2, Nat, xs, [_]) : List<&2, Nat>}
  {==}

# line 0 starts at 2·B(r)
def pa.vlast(d: Bool, +r: Nat) -> {O.Bits.val(O.pair_start(pa.line(d, r))) == Nat.double(r) : Nat}:
  match d:
    case False{}:
      pa.val_nb(Nat.double(r))
    case True{}:
      Equal.cong(Nat, Nat, z => Nat.double(z), O.Bits.val(pa.nb(r)), r, pa.val_nb(r))

def pa.sv_l(+d: Bool, +r: List<&2, Bool>, ih: {pa.SG(r) == pa.rev(pa.SE(r, 0n)) : List<&2, Nat>}) -> {pa.SG(d <> r) == List.append(&2, Nat, pa.dbls(pa.rev(pa.SE(r, 0n))), [Nat.double(pa.B(r))]) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, pa.SG(d <> r), List.append(&2, Nat, pa.vals(O.starts(pa.lifts(pa.GV(r)))), [O.Bits.val(O.pair_start(pa.line(d, pa.B(r))))]), List.append(&2, Nat, pa.dbls(pa.rev(pa.SE(r, 0n))), [Nat.double(pa.B(r))]),
    pa.vs_app(pa.lifts(pa.GV(r)), pa.line(d, pa.B(r))),
    pa.app2(pa.vals(O.starts(pa.lifts(pa.GV(r)))), pa.dbls(pa.rev(pa.SE(r, 0n))), O.Bits.val(O.pair_start(pa.line(d, pa.B(r)))), Nat.double(pa.B(r)),
      Equal.trans(List<&2, Nat>, pa.vals(O.starts(pa.lifts(pa.GV(r)))), pa.dbls(pa.SG(r)), pa.dbls(pa.rev(pa.SE(r, 0n))), pa.vs_lifts(pa.GV(r)), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => pa.dbls(z), pa.SG(r), pa.rev(pa.SE(r, 0n)), ih)),
      pa.vlast(d, pa.B(r))))

def pa.sv_r(+r: List<&2, Bool>, +v1: Nat, e1: {v1 == Nat.double(pa.B(r)) : Nat}) -> {List.reverse.go(&2, Nat, pa.SE(r, 1n), [v1]) == List.append(&2, Nat, pa.dbls(pa.rev(pa.SE(r, 0n))), [Nat.double(pa.B(r))]) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, List.reverse.go(&2, Nat, pa.SE(r, 1n), [v1]), List.append(&2, Nat, pa.rev(pa.SE(r, 1n)), [v1]), List.append(&2, Nat, pa.dbls(pa.rev(pa.SE(r, 0n))), [Nat.double(pa.B(r))]),
    pa.rev_app(pa.SE(r, 1n), [v1]),
    pa.app2(pa.rev(pa.SE(r, 1n)), pa.dbls(pa.rev(pa.SE(r, 0n))), v1, Nat.double(pa.B(r)),
      Equal.trans(List<&2, Nat>, pa.rev(pa.SE(r, 1n)), pa.rev(pa.dbls(pa.SE(r, 0n))), pa.dbls(pa.rev(pa.SE(r, 0n))), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => pa.rev(z), pa.SE(r, 1n), pa.dbls(pa.SE(r, 0n)), pa.vst(r, 0n)), pa.dbls_rev(pa.SE(r, 0n), Nil{})),
      e1))

# the view's starts are push's states, oldest first
def pa.sv(ds: List<&2, Bool>) -> {pa.SG(ds) == pa.rev(pa.SE(ds, 0n)) : List<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          Equal.trans(List<&2, Nat>, pa.SG(False{} <> r), List.append(&2, Nat, pa.dbls(pa.rev(pa.SE(r, 0n))), [Nat.double(pa.B(r))]), pa.rev(pa.SE(False{} <> r, 0n)), pa.sv_l(False{}, r, pa.sv(r)), Equal.sym(List<&2, Nat>, pa.rev(pa.SE(False{} <> r, 0n)), List.append(&2, Nat, pa.dbls(pa.rev(pa.SE(r, 0n))), [Nat.double(pa.B(r))]), pa.sv_r(r, O.Bits.val(pa.nb(pa.sh(1n, pa.B(r)))), pa.val_nb(pa.sh(1n, pa.B(r))))))
        case True{}:
          Equal.trans(List<&2, Nat>, pa.SG(True{} <> r), List.append(&2, Nat, pa.dbls(pa.rev(pa.SE(r, 0n))), [Nat.double(pa.B(r))]), pa.rev(pa.SE(True{} <> r, 0n)), pa.sv_l(True{}, r, pa.sv(r)), Equal.sym(List<&2, Nat>, pa.rev(pa.SE(True{} <> r, 0n)), List.append(&2, Nat, pa.dbls(pa.rev(pa.SE(r, 0n))), [Nat.double(pa.B(r))]), pa.sv_r(r, O.Bits.val(pa.nb(pa.sh(1n, pa.B(r)))), pa.val_nb(pa.sh(1n, pa.B(r))))))

def pa.same_lines(+ds: List<&2, Bool>) -> {O.same_lines(pa.GV(ds), pa.GE(ds, 0n)) == True{} : Bool}:
  pa.same_vals(O.starts(pa.GV(ds)), List.reverse.go(&2, List<&2, Bool>, O.states(pa.GE(ds, 0n)), Nil{}), Equal.trans(List<&2, Nat>, pa.SG(ds), pa.rev(pa.SE(ds, 0n)), pa.vals(List.reverse.go(&2, List<&2, Bool>, O.states(pa.GE(ds, 0n)), Nil{})), pa.sv(ds), Equal.sym(List<&2, Nat>, pa.vals(List.reverse.go(&2, List<&2, Bool>, O.states(pa.GE(ds, 0n)), Nil{})), pa.rev(pa.SE(ds, 0n)), pa.vals_rev(O.states(pa.GE(ds, 0n)), Nil{}))))

# Sizes
# -----
# Under push every line counts 1 and every node is built (All{1}).

def pa.vs(v: List<&2, O.Node>) -> Nat:
  O.view_size(0n, O.All{1n}, v)

def pa.len_GE(ds: List<&2, Bool>, +j: Nat) -> {List.length(&2, O.Entry, pa.GE(ds, j)) == List.length(&2, Bool, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          L.pa.succ(List.length(&2, O.Entry, pa.GE(r, 1n+j)), List.length(&2, Bool, r), pa.len_GE(r, 1n+j))
        case True{}:
          L.pa.succ(List.length(&2, O.Entry, pa.GE(r, 1n+j)), List.length(&2, Bool, r), pa.len_GE(r, 1n+j))

def pa.len_app1(xs: List<&2, O.Node>, -y: O.Node) -> {List.length(&2, O.Node, List.append(&2, O.Node, xs, [y])) == 1n+List.length(&2, O.Node, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      L.pa.succ(List.length(&2, O.Node, List.append(&2, O.Node, t, [y])), 1n+List.length(&2, O.Node, t), pa.len_app1(t, y))

def pa.len_lifts(xs: List<&2, O.Node>) -> {List.length(&2, O.Node, pa.lifts(xs)) == List.length(&2, O.Node, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      L.pa.succ(List.length(&2, O.Node, pa.lifts(t)), List.length(&2, O.Node, t), pa.len_lifts(t))

def pa.len_GV(ds: List<&2, Bool>) -> {List.length(&2, O.Node, pa.GV(ds)) == List.length(&2, Bool, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +r:
      Equal.trans(Nat, List.length(&2, O.Node, pa.GV(d <> r)), 1n+List.length(&2, O.Node, pa.lifts(pa.GV(r))), 1n+List.length(&2, Bool, r),
        pa.len_app1(pa.lifts(pa.GV(r)), pa.line(d, pa.B(r))),
        L.pa.succ(List.length(&2, O.Node, pa.lifts(pa.GV(r))), List.length(&2, Bool, r), Equal.trans(Nat, List.length(&2, O.Node, pa.lifts(pa.GV(r))), List.length(&2, O.Node, pa.GV(r)), List.length(&2, Bool, r), pa.len_lifts(pa.GV(r)), pa.len_GV(r))))

def pa.size_app(xs: List<&2, O.Node>, +ys: List<&2, O.Node>) -> {pa.vs(List.append(&2, O.Node, xs, ys)) == Nat.add(pa.vs(ys), List.length(&2, O.Node, xs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(pa.vs(ys), 0n), pa.vs(ys), L.pa.add_zero(pa.vs(ys)))
    case h <> +t:
      Equal.trans(Nat, 1n+pa.vs(List.append(&2, O.Node, t, ys)), 1n+Nat.add(pa.vs(ys), List.length(&2, O.Node, t)), Nat.add(pa.vs(ys), 1n+List.length(&2, O.Node, t)),
        L.pa.succ(pa.vs(List.append(&2, O.Node, t, ys)), Nat.add(pa.vs(ys), List.length(&2, O.Node, t)), pa.size_app(t, ys)),
        Equal.sym(Nat, Nat.add(pa.vs(ys), 1n+List.length(&2, O.Node, t)), 1n+Nat.add(pa.vs(ys), List.length(&2, O.Node, t)), L.pa.add_succ(pa.vs(ys), List.length(&2, O.Node, t))))

# the higher lines of the view of r, then ys
def pa.size_hi(+r: List<&2, Bool>, +ys: List<&2, O.Node>) -> {pa.vs(List.append(&2, O.Node, pa.lifts(pa.GV(r)), ys)) == Nat.add(pa.vs(ys), List.length(&2, Bool, r)) : Nat}:
  Equal.trans(Nat, pa.vs(List.append(&2, O.Node, pa.lifts(pa.GV(r)), ys)), Nat.add(pa.vs(ys), List.length(&2, O.Node, pa.lifts(pa.GV(r)))), Nat.add(pa.vs(ys), List.length(&2, Bool, r)),
    pa.size_app(pa.lifts(pa.GV(r)), ys),
    Equal.cong(Nat, Nat, z => Nat.add(pa.vs(ys), z), List.length(&2, O.Node, pa.lifts(pa.GV(r))), List.length(&2, Bool, r), Equal.trans(Nat, List.length(&2, O.Node, pa.lifts(pa.GV(r))), List.length(&2, O.Node, pa.GV(r)), List.length(&2, Bool, r), pa.len_lifts(pa.GV(r)), pa.len_GV(r))))

def pa.snd_cons(-n: O.Node, r: List<&2, O.Node> & List<&2, O.Node>) -> {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, r) == Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.cons(n, r)) : List<&2, O.Node>}:
  (ms, out) = r
  {==}

# One level up
# ------------
# up(V, z): every line of V one level up, then a level-0 line z. With
# T + 2 doubled, the due order between lifted lines is the old one, so a
# fit of up(V, z) is the lifted fit of V.

def pa.up(v: List<&2, O.Node>, +z: O.Node) -> List<&2, O.Node>:
  List.append(&2, O.Node, pa.lifts(v), [z])

def pa.liftm(m: Maybe<&2, O.Node>) -> Maybe<&2, O.Node>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{pa.lift(x)}

def pa.shl_cons(l: Nat, +x: List<&2, Bool>) -> {O.Bits.shl(l, False{} <> x) == False{} <> O.Bits.shl(l, x) : List<&2, Bool>}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, z => False{} <> z, O.Bits.shl(p, False{} <> x), False{} <> O.Bits.shl(p, x), pa.shl_cons(p, x))

def pa.shl_ff(+l: Nat, +x: List<&2, Bool>) -> {False{} <> False{} <> O.Bits.shl(l, x) == O.Bits.shl(1n+l, False{} <> x) : List<&2, Bool>}:
  Equal.sym(List<&2, Bool>, O.Bits.shl(1n+l, False{} <> x), False{} <> False{} <> O.Bits.shl(l, x), Equal.cong(List<&2, Bool>, List<&2, Bool>, z => False{} <> z, O.Bits.shl(l, False{} <> x), False{} <> O.Bits.shl(l, x), pa.shl_cons(l, x)))

def pa.gt_ff(c: Cmp) -> {Cmp.is_gt(O.Cmp.then(O.Cmp.then(c, EQ{}), EQ{})) == Cmp.is_gt(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# both sides of the cross comparison times 4
def pa.cross_lift(+u: List<&2, Bool>, +la: Nat, +lb: Nat, +xa: List<&2, Bool>, +xb: List<&2, Bool>) -> {O.more_due.cross(False{} <> u, 1n+la, 1n+lb, False{} <> xa, False{} <> xb) == O.more_due.cross(u, la, lb, xa, xb) : Bool}:
  %pa.shl_ff(lb, u) : {O.Bits.gt(O.Bits.add(_, O.Bits.shl(1n+la, False{} <> xb)), O.Bits.add(O.Bits.shl(1n+la, False{} <> u), O.Bits.shl(1n+lb, False{} <> xa))) == O.more_due.cross(u, la, lb, xa, xb) : Bool}
  %pa.shl_ff(la, xb) : {O.Bits.gt(O.Bits.add(False{} <> False{} <> O.Bits.shl(lb, u), _), O.Bits.add(O.Bits.shl(1n+la, False{} <> u), O.Bits.shl(1n+lb, False{} <> xa))) == O.more_due.cross(u, la, lb, xa, xb) : Bool}
  %pa.shl_ff(la, u) : {O.Bits.gt(O.Bits.add(False{} <> False{} <> O.Bits.shl(lb, u), False{} <> False{} <> O.Bits.shl(la, xb)), O.Bits.add(_, O.Bits.shl(1n+lb, False{} <> xa))) == O.more_due.cross(u, la, lb, xa, xb) : Bool}
  %pa.shl_ff(lb, xa) : {O.Bits.gt(O.Bits.add(False{} <> False{} <> O.Bits.shl(lb, u), False{} <> False{} <> O.Bits.shl(la, xb)), O.Bits.add(False{} <> False{} <> O.Bits.shl(la, u), _)) == O.more_due.cross(u, la, lb, xa, xb) : Bool}
  pa.gt_ff(O.Bits.cmp(O.Bits.add(O.Bits.shl(lb, u), O.Bits.shl(la, xb)), O.Bits.add(O.Bits.shl(la, u), O.Bits.shl(lb, xa))))

# hu: T + 2 is twice T0 + 2
def pa.md_lift(+x: O.Node, +c: O.Node, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> O.Bits.inc(t0) == O.Bits.inc(t) : List<&2, Bool>})
  -> {O.more_due(O.Last{}, t, pa.lift(x), pa.lift(c)) == O.more_due(O.Last{}, t0, x, c) : Bool}:
  match x c:
    case O.Node{+lx, +ix} O.Node{+lc, +ic}:
      %hu : {O.more_due.cross(_, 1n+lx, 1n+lc, False{} <> O.pair_end(O.Node{lx, ix}), False{} <> O.pair_end(O.Node{lc, ic})) == O.more_due(O.Last{}, t0, O.Node{lx, ix}, O.Node{lc, ic}) : Bool}
      pa.cross_lift(O.Bits.inc(t0), lx, lc, O.pair_end(O.Node{lx, ix}), O.pair_end(O.Node{lc, ic}))

def pa.vs_lift(b: Bool, -x: O.Node, -c: O.Node) -> {O.best.vs(b, pa.lift(x), pa.lift(c)) == pa.lift(O.best.vs(b, x, c)) : O.Node}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pa.take_lift(cur: Maybe<&2, O.Node>, +x: O.Node, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> O.Bits.inc(t0) == O.Bits.inc(t) : List<&2, Bool>})
  -> {O.best.take(O.Last{}, t, pa.lift(x), pa.liftm(cur)) == pa.liftm(O.best.take(O.Last{}, t0, x, cur)) : Maybe<&2, O.Node>}:
  match cur:
    case None{}:
      {==}
    case Some{+c}:
      %Equal.sym(Bool, O.more_due(O.Last{}, t, pa.lift(x), pa.lift(c)), O.more_due(O.Last{}, t0, x, c), pa.md_lift(x, c, t, t0, hu)) : {Some{O.best.vs(_, pa.lift(x), pa.lift(c))} == Some{pa.lift(O.best.vs(O.more_due(O.Last{}, t0, x, c), x, c))} : Maybe<&2, O.Node>}
      Equal.cong(O.Node, Maybe<&2, O.Node>, z => Some{z}, O.best.vs(O.more_due(O.Last{}, t0, x, c), pa.lift(x), pa.lift(c)), pa.lift(O.best.vs(O.more_due(O.Last{}, t0, x, c), x, c)), pa.vs_lift(O.more_due(O.Last{}, t0, x, c), x, c))

def pa.pick_lift(ok: Bool, +cur: Maybe<&2, O.Node>, +x: O.Node, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> O.Bits.inc(t0) == O.Bits.inc(t) : List<&2, Bool>})
  -> {O.best.pick(ok, O.Last{}, t, pa.lift(x), pa.liftm(cur)) == pa.liftm(O.best.pick(ok, O.Last{}, t0, x, cur)) : Maybe<&2, O.Node>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      pa.take_lift(cur, x, t, t0, hu)

# the pair of x and the next line is mergeable in up(V, z) as in V; the
# last lifted line and z never are (z is level 0)
def pa.pair_lift(v: List<&2, O.Node>, +x: O.Node, +cur: Maybe<&2, O.Node>, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> O.Bits.inc(t0) == O.Bits.inc(t) : List<&2, Bool>})
  -> {O.best.pair(O.Last{}, t, O.All{1n}, pa.lift(x), List.head(&2, O.Node, pa.up(v, O.Node{0n, iz})), pa.liftm(cur)) == pa.liftm(O.best.pair(O.Last{}, t0, O.All{1n}, x, List.head(&2, O.Node, v), cur)) : Maybe<&2, O.Node>}:
  match v x:
    case Nil{} O.Node{lx, ix}:
      {==}
    case O.Node{+ly, +iy} <> w O.Node{+lx, +ix}:
      pa.pick_lift(O.mergeable(O.All{1n}, O.Node{lx, ix}, O.Node{ly, iy}), cur, O.Node{lx, ix}, t, t0, hu)

def pa.best_lift(v: List<&2, O.Node>, +cur: Maybe<&2, O.Node>, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> O.Bits.inc(t0) == O.Bits.inc(t) : List<&2, Bool>})
  -> {O.best.go(O.Last{}, t, O.All{1n}, pa.up(v, O.Node{0n, iz}), pa.liftm(cur)) == pa.liftm(O.best.go(O.Last{}, t0, O.All{1n}, v, cur)) : Maybe<&2, O.Node>}:
  match v:
    case Nil{}:
      {==}
    case +x <> +w:
      %Equal.sym(Maybe<&2, O.Node>, O.best.pair(O.Last{}, t, O.All{1n}, pa.lift(x), List.head(&2, O.Node, pa.up(w, O.Node{0n, iz})), pa.liftm(cur)), pa.liftm(O.best.pair(O.Last{}, t0, O.All{1n}, x, List.head(&2, O.Node, w), cur)), pa.pair_lift(w, x, cur, iz, t, t0, hu)) : {O.best.go(O.Last{}, t, O.All{1n}, pa.up(w, O.Node{0n, iz}), _) == pa.liftm(O.best.go(O.Last{}, t0, O.All{1n}, x <> w, cur)) : Maybe<&2, O.Node>}
      pa.best_lift(w, O.best.pair(O.Last{}, t0, O.All{1n}, x, List.head(&2, O.Node, w), cur), iz, t, t0, hu)

def pa.mpick_lift(h: Bool, +x: O.Node, +y: O.Node, +w: List<&2, O.Node>, +rec: List<&2, O.Node>, +z: O.Node)
  -> {O.merge.pick(h, pa.lift(x), pa.lift(y), pa.up(w, z), pa.up(rec, z)) == pa.up(O.merge.pick(h, x, y, w, rec), z) : List<&2, O.Node>}:
  match h x:
    case True{} O.Node{lx, ix}:
      {==}
    case False{} O.Node{lx, ix}:
      {==}

def pa.mpick_nil(h: Bool, +x: O.Node, +z: O.Node) -> {O.merge.pick(Bool.and(h, False{}), x, z, Nil{}, [z]) == [x, z] : List<&2, O.Node>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def pa.here_lift(w: List<&2, O.Node>, +x: O.Node, +a: O.Node, +iz: List<&2, Bool>)
  -> {O.merge.here(O.All{1n}, pa.lift(a), pa.lift(x), pa.up(w, O.Node{0n, iz}), pa.up(O.merge(O.All{1n}, w, a), O.Node{0n, iz})) == pa.up(O.merge.here(O.All{1n}, a, x, w, O.merge(O.All{1n}, w, a)), O.Node{0n, iz}) : List<&2, O.Node>}:
  match w x a:
    case Nil{} O.Node{+lx, +ix} O.Node{+la, +ia}:
      pa.mpick_nil(O.Node.eq(O.Node{lx, ix}, O.Node{la, ia}), O.Node{1n+lx, ix}, O.Node{0n, iz})
    case O.Node{+ly, +iy} <> +v O.Node{+lx, +ix} O.Node{+la, +ia}:
      pa.mpick_lift(Bool.and(O.Node.eq(O.Node{lx, ix}, O.Node{la, ia}), O.mergeable(O.All{1n}, O.Node{lx, ix}, O.Node{ly, iy})), O.Node{lx, ix}, O.Node{ly, iy}, v, O.merge(O.All{1n}, O.Node{ly, iy} <> v, O.Node{la, ia}), O.Node{0n, iz})

def pa.merge_lift(v: List<&2, O.Node>, +a: O.Node, +iz: List<&2, Bool>) -> {O.merge(O.All{1n}, pa.up(v, O.Node{0n, iz}), pa.lift(a)) == pa.up(O.merge(O.All{1n}, v, a), O.Node{0n, iz}) : List<&2, O.Node>}:
  match v:
    case Nil{}:
      {==}
    case +x <> +w:
      %Equal.sym(List<&2, O.Node>, O.merge(O.All{1n}, pa.up(w, O.Node{0n, iz}), pa.lift(a)), pa.up(O.merge(O.All{1n}, w, a), O.Node{0n, iz}), pa.merge_lift(w, a, iz)) : {O.merge.here(O.All{1n}, pa.lift(a), pa.lift(x), pa.up(w, O.Node{0n, iz}), _) == pa.up(O.merge(O.All{1n}, x <> w, a), O.Node{0n, iz}) : List<&2, O.Node>}
      pa.here_lift(w, x, a, iz)

def pa.size_up(v: List<&2, O.Node>, +z: O.Node) -> {pa.vs(pa.up(v, z)) == 1n+pa.vs(v) : Nat}:
  match v:
    case Nil{}:
      {==}
    case h <> w:
      L.pa.succ(pa.vs(pa.up(w, z)), 1n+pa.vs(w), pa.size_up(w, z))

def pa.cif_lift(over: Bool, +v: List<&2, O.Node>, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> O.Bits.inc(t0) == O.Bits.inc(t) : List<&2, Bool>})
  -> {O.choose.if(over, O.Last{}, t, O.All{1n}, pa.up(v, O.Node{0n, iz})) == pa.liftm(O.choose.if(over, O.Last{}, t0, O.All{1n}, v)) : Maybe<&2, O.Node>}:
  match over:
    case False{}:
      {==}
    case True{}:
      pa.best_lift(v, None{}, iz, t, t0, hu)

def pa.choose_lift(+v: List<&2, O.Node>, +b: Nat, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> O.Bits.inc(t0) == O.Bits.inc(t) : List<&2, Bool>})
  -> {O.choose(O.Last{}, t, 1n+b, 0n, O.All{1n}, pa.up(v, O.Node{0n, iz})) == pa.liftm(O.choose(O.Last{}, t0, b, 0n, O.All{1n}, v)) : Maybe<&2, O.Node>}:
  %Equal.sym(Nat, pa.vs(pa.up(v, O.Node{0n, iz})), 1n+pa.vs(v), pa.size_up(v, O.Node{0n, iz})) : {O.choose.if(Nat.is_gt(_, 1n+b), O.Last{}, t, O.All{1n}, pa.up(v, O.Node{0n, iz})) == pa.liftm(O.choose(O.Last{}, t0, b, 0n, O.All{1n}, v)) : Maybe<&2, O.Node>}
  pa.cif_lift(Nat.is_gt(pa.vs(v), b), v, iz, t, t0, hu)

def pa.fit_lift(f: Nat, c: Maybe<&2, O.Node>, +v: List<&2, O.Node>, +b: Nat, +iz: List<&2, Bool>, +t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> O.Bits.inc(t0) == O.Bits.inc(t) : List<&2, Bool>})
  -> {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(f, pa.liftm(c), O.Last{}, t, 1n+b, 0n, O.All{1n}, pa.up(v, O.Node{0n, iz}))) == pa.up(Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(f, c, O.Last{}, t0, b, 0n, O.All{1n}, v)), O.Node{0n, iz}) : List<&2, O.Node>}:
  match f c:
    case 0n _:
      {==}
    case 1n+g None{}:
      {==}
    case 1n++g Some{+a}:
      +m0 = O.merge(O.All{1n}, v, a)
      r0 = O.fit.go(g, O.choose(O.Last{}, t0, b, 0n, O.All{1n}, m0), O.Last{}, t0, b, 0n, O.All{1n}, m0)
      %pa.snd_cons(O.Node.parent(pa.lift(a)), O.fit.go(g, O.choose(O.Last{}, t, 1n+b, 0n, O.All{1n}, O.merge(O.All{1n}, pa.up(v, O.Node{0n, iz}), pa.lift(a))), O.Last{}, t, 1n+b, 0n, O.All{1n}, O.merge(O.All{1n}, pa.up(v, O.Node{0n, iz}), pa.lift(a)))) : {_ == pa.up(Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.cons(O.Node.parent(a), r0)), O.Node{0n, iz}) : List<&2, O.Node>}
      %pa.snd_cons(O.Node.parent(a), r0) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(g, O.choose(O.Last{}, t, 1n+b, 0n, O.All{1n}, O.merge(O.All{1n}, pa.up(v, O.Node{0n, iz}), pa.lift(a))), O.Last{}, t, 1n+b, 0n, O.All{1n}, O.merge(O.All{1n}, pa.up(v, O.Node{0n, iz}), pa.lift(a)))) == pa.up(_, O.Node{0n, iz}) : List<&2, O.Node>}
      %Equal.sym(List<&2, O.Node>, O.merge(O.All{1n}, pa.up(v, O.Node{0n, iz}), pa.lift(a)), pa.up(m0, O.Node{0n, iz}), pa.merge_lift(v, a, iz)) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(g, O.choose(O.Last{}, t, 1n+b, 0n, O.All{1n}, _), O.Last{}, t, 1n+b, 0n, O.All{1n}, _)) == pa.up(Pair.snd(List<&2, O.Node>, List<&2, O.Node>, r0), O.Node{0n, iz}) : List<&2, O.Node>}
      %Equal.sym(Maybe<&2, O.Node>, O.choose(O.Last{}, t, 1n+b, 0n, O.All{1n}, pa.up(m0, O.Node{0n, iz})), pa.liftm(O.choose(O.Last{}, t0, b, 0n, O.All{1n}, m0)), pa.choose_lift(m0, b, iz, t, t0, hu)) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(g, _, O.Last{}, t, 1n+b, 0n, O.All{1n}, pa.up(m0, O.Node{0n, iz}))) == pa.up(Pair.snd(List<&2, O.Node>, List<&2, O.Node>, r0), O.Node{0n, iz}) : List<&2, O.Node>}
      pa.fit_lift(g, O.choose(O.Last{}, t0, b, 0n, O.All{1n}, m0), m0, b, iz, t, t0, hu)

# Older lines end late enough
# ---------------------------
# Good(c, R): line c = node(l, i) of the view of R messages has
# (i + 3)·2^l >= R + 2, i.e. it ends at most 2^(l+1) - 2 messages before
# R: what follows it is at most two lines per lower level.

def pa.Good(c: O.Node, +R: Nat) -> Type:
  match c:
    case O.Node{l, i}:
      &k:Nat -> {pa.sh(l, 3n+O.Bits.val(i)) == Nat.add(k, 2n+R) : Nat}

def pa.GoodAll(+R: Nat, xs: List<&2, O.Node>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case c <> t:
      (pa.Good(c, R) & pa.GoodAll(R, t))

# B(d <> r) from B(r), and the slack one level up
def pa.Bd(d: Bool, +R: Nat) -> Nat:
  match d:
    case False{}:
      1n+Nat.double(R)
    case True{}:
      2n+Nat.double(R)

def pa.bit_k(d: Bool, +k: Nat) -> Nat:
  match d:
    case False{}:
      1n+Nat.double(k)
    case True{}:
      Nat.double(k)

def pa.good_lift.eq(d: Bool, +k: Nat, +R: Nat, -S: Nat, e: {Nat.double(S) == Nat.add(Nat.double(k), 4n+Nat.double(R)) : Nat})
  -> {Nat.double(S) == Nat.add(pa.bit_k(d, k), 2n+pa.Bd(d, R)) : Nat}:
  match d:
    case False{}:
      Equal.trans(Nat, Nat.double(S), Nat.add(Nat.double(k), 4n+Nat.double(R)), 1n+Nat.add(Nat.double(k), 3n+Nat.double(R)), e, L.pa.add_succ(Nat.double(k), 3n+Nat.double(R)))
    case True{}:
      e

def pa.good_lift(+d: Bool, c: O.Node, +R: Nat, g: pa.Good(c, R)) -> pa.Good(pa.lift(c), pa.Bd(d, R)):
  match c:
    case O.Node{+l, +i}:
      (k0, e) = g
      +k = k0
      (pa.bit_k(d, k), pa.good_lift.eq(d, k, R, pa.sh(l, 3n+O.Bits.val(i)), Equal.trans(Nat, Nat.double(pa.sh(l, 3n+O.Bits.val(i))), Nat.double(Nat.add(k, 2n+R)), Nat.add(Nat.double(k), 4n+Nat.double(R)), Equal.cong(Nat, Nat, z => Nat.double(z), pa.sh(l, 3n+O.Bits.val(i)), Nat.add(k, 2n+R), e), pa.double_add(k, 2n+R))))

def pa.goods_lift(+d: Bool, xs: List<&2, O.Node>, +R: Nat, g: pa.GoodAll(R, xs)) -> pa.GoodAll(pa.Bd(d, R), pa.lifts(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case c <> t:
      (gc, gt) = g
      (pa.good_lift(d, c, R, gc), pa.goods_lift(d, t, R, gt))

def pa.good_line(d: Bool, +R: Nat) -> pa.Good(pa.line(d, R), pa.Bd(d, R)):
  match d:
    case False{}:
      (0n, Equal.cong(Nat, Nat, z => 3n+z, O.Bits.val(pa.nb(Nat.double(R))), Nat.double(R), pa.val_nb(Nat.double(R))))
    case True{}:
      (2n, Equal.cong(Nat, Nat, z => Nat.double(3n+z), O.Bits.val(pa.nb(R)), R, pa.val_nb(R)))

def pa.good_app(xs: List<&2, O.Node>, -y: O.Node, -R: Nat, gx: pa.GoodAll(R, xs), gy: pa.Good(y, R)) -> pa.GoodAll(R, List.append(&2, O.Node, xs, [y])):
  match xs:
    case Nil{}:
      (gy, Unit{})
    case c <> t:
      (gc, gt) = gx
      (gc, pa.good_app(t, y, R, gt, gy))

def pa.good_gv(ds: List<&2, Bool>) -> pa.GoodAll(pa.B(ds), pa.GV(ds)):
  match ds:
    case Nil{}:
      Unit{}
    case d <> +r:
      match d:
        case False{}:
          pa.good_app(pa.lifts(pa.GV(r)), pa.line(False{}, pa.B(r)), pa.Bd(False{}, pa.B(r)), pa.goods_lift(False{}, pa.GV(r), pa.B(r), pa.good_gv(r)), pa.good_line(False{}, pa.B(r)))
        case True{}:
          pa.good_app(pa.lifts(pa.GV(r)), pa.line(True{}, pa.B(r)), pa.Bd(True{}, pa.B(r)), pa.goods_lift(True{}, pa.GV(r), pa.B(r), pa.good_gv(r)), pa.good_line(True{}, pa.B(r)))

# The newest pair is the most due
# -------------------------------
# With the lowest digit 0, T = 1 + 2R: line 0 is a0 = node(0, 2R), the new
# line b0 = node(0, 2R + 1), and the pair is due (T - last)/1 = 1. The
# older lines are the view of R lifted, each due less than 1 by Good:
# in the cross form, 2^l·(T + 2) + e_c > (T + 2) + 2^l·e_a.

def pa.a0(+R: Nat) -> O.Node:
  O.Node{0n, pa.nb(Nat.double(R))}

def pa.b0(+R: Nat) -> O.Node:
  O.Node{0n, True{} <> pa.nb(R)}

# T + 1 in binary, T = 1 + 2R
def pa.tb0(+R: Nat) -> List<&2, Bool>:
  O.Bits.inc(True{} <> pa.nb(R))

def pa.add2(-a: Nat, -a2: Nat, -b: Nat, -b2: Nat, e1: {a == a2 : Nat}, e2: {b == b2 : Nat}) -> {Nat.add(a, b) == Nat.add(a2, b2) : Nat}:
  %e1 : {Nat.add(a, b) == Nat.add(_, b2) : Nat}
  %e2 : {Nat.add(a, b) == Nat.add(a, _) : Nat}
  {==}

def pa.swap_mid(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, c), b),
    pa.add_assoc(a, b, c),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b),
      Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, c), Nat.add(c, b), L.pa.add_comm(b, c)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), pa.add_assoc(a, c, b))))

# 2·2^l·(R + 3/2) + 2·2^l·(i + 2) = (3 + 2R + 2·2^l·(R + 1)) + 1 + 2k
def pa.ineq(+l: Nat, +R: Nat, +vi: Nat, +k: Nat, e: {pa.sh(l, 3n+vi) == Nat.add(k, 2n+R) : Nat})
  -> {Nat.add(Nat.double(pa.sh(l, 3n+Nat.double(R))), Nat.double(pa.sh(l, 2n+vi))) == Nat.add(Nat.add(3n+Nat.double(R), Nat.double(pa.sh(l, 2n+Nat.double(R)))), 1n+Nat.double(k)) : Nat}:
  +A = pa.sh(l, 1n)
  +P = pa.sh(l, 2n+Nat.double(R))
  +S = pa.sh(l, 2n+vi)
  +dA = Nat.double(A)
  +dP = Nat.double(P)
  +dS = Nat.double(S)
  +dk = Nat.double(k)
  +Y = Nat.add(3n+Nat.double(R), dP)
  -L0 = Nat.add(Nat.double(pa.sh(l, 3n+Nat.double(R))), dS)
  -L1 = Nat.add(Nat.double(Nat.add(A, P)), dS)
  -L2 = Nat.add(Nat.add(dA, dP), dS)
  -L3 = Nat.add(Nat.add(dA, dS), dP)
  -L4 = Nat.add(Nat.double(Nat.add(A, S)), dP)
  -L5 = Nat.add(Nat.double(Nat.add(k, 2n+R)), dP)
  -L6 = Nat.add(Nat.add(dk, 4n+Nat.double(R)), dP)
  -L7 = Nat.add(Nat.add(4n+Nat.double(R), dk), dP)
  -L8 = Nat.add(Nat.add(4n+Nat.double(R), dP), dk)
  -L9 = Nat.add(Y, 1n+dk)
  hs = Equal.trans(Nat, Nat.add(A, S), pa.sh(l, 3n+vi), Nat.add(k, 2n+R), Equal.sym(Nat, pa.sh(l, 3n+vi), Nat.add(A, S), pa.sh_add(l, 1n, 2n+vi)), e)
  c1 = Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), dS), pa.sh(l, 3n+Nat.double(R)), Nat.add(A, P), pa.sh_add(l, 1n, 2n+Nat.double(R)))
  c2 = Equal.trans(Nat, L0, L1, L2, c1, Equal.cong(Nat, Nat, z => Nat.add(z, dS), Nat.double(Nat.add(A, P)), Nat.add(dA, dP), pa.double_add(A, P)))
  c3 = Equal.trans(Nat, L0, L2, L3, c2, pa.swap_mid(dA, dP, dS))
  c4 = Equal.trans(Nat, L0, L3, L4, c3, Equal.cong(Nat, Nat, z => Nat.add(z, dP), Nat.add(dA, dS), Nat.double(Nat.add(A, S)), Equal.sym(Nat, Nat.double(Nat.add(A, S)), Nat.add(dA, dS), pa.double_add(A, S))))
  c5 = Equal.trans(Nat, L0, L4, L5, c4, Equal.cong(Nat, Nat, z => Nat.add(Nat.double(z), dP), Nat.add(A, S), Nat.add(k, 2n+R), hs))
  c6 = Equal.trans(Nat, L0, L5, L6, c5, Equal.cong(Nat, Nat, z => Nat.add(z, dP), Nat.double(Nat.add(k, 2n+R)), Nat.add(dk, 4n+Nat.double(R)), pa.double_add(k, 2n+R)))
  c7 = Equal.trans(Nat, L0, L6, L7, c6, Equal.cong(Nat, Nat, z => Nat.add(z, dP), Nat.add(dk, 4n+Nat.double(R)), Nat.add(4n+Nat.double(R), dk), L.pa.add_comm(dk, 4n+Nat.double(R))))
  c8 = Equal.trans(Nat, L0, L7, L8, c7, pa.swap_mid(4n+Nat.double(R), dk, dP))
  Equal.trans(Nat, L0, L8, L9, c8, Equal.sym(Nat, L9, 1n+Nat.add(Y, dk), L.pa.add_succ(Y, dk)))

def pa.vii(+i: List<&2, Bool>) -> {O.Bits.val(O.Bits.inc(O.Bits.inc(i))) == 2n+O.Bits.val(i) : Nat}:
  Equal.trans(Nat, O.Bits.val(O.Bits.inc(O.Bits.inc(i))), 1n+O.Bits.val(O.Bits.inc(i)), 2n+O.Bits.val(i), pa.val_inc(O.Bits.inc(i)), L.pa.succ(O.Bits.val(O.Bits.inc(i)), 1n+O.Bits.val(i), pa.val_inc(i)))

# T + 2 = 3 + 2R
def pa.vu(+R: Nat) -> {O.Bits.val(True{} <> O.Bits.inc(pa.nb(R))) == 3n+Nat.double(R) : Nat}:
  Equal.cong(Nat, Nat, z => 1n+Nat.double(z), O.Bits.val(O.Bits.inc(pa.nb(R))), 1n+R, Equal.trans(Nat, O.Bits.val(O.Bits.inc(pa.nb(R))), 1n+O.Bits.val(pa.nb(R)), 1n+R, pa.val_inc(pa.nb(R)), L.pa.succ(O.Bits.val(pa.nb(R)), R, pa.val_nb(R))))

def pa.vX(+l: Nat, +R: Nat, +i: List<&2, Bool>)
  -> {O.Bits.val(O.Bits.add(False{} <> O.Bits.shl(l, True{} <> O.Bits.inc(pa.nb(R))), False{} <> O.Bits.shl(l, O.Bits.inc(O.Bits.inc(i))))) == Nat.add(Nat.double(pa.sh(l, 3n+Nat.double(R))), Nat.double(pa.sh(l, 2n+O.Bits.val(i)))) : Nat}:
  +U = {True{} <> O.Bits.inc(pa.nb(R)) : List<&2, Bool>}
  +II = O.Bits.inc(O.Bits.inc(i))
  Equal.trans(Nat, O.Bits.val(O.Bits.add(False{} <> O.Bits.shl(l, U), False{} <> O.Bits.shl(l, II))), Nat.add(Nat.double(O.Bits.val(O.Bits.shl(l, U))), Nat.double(O.Bits.val(O.Bits.shl(l, II)))), Nat.add(Nat.double(pa.sh(l, 3n+Nat.double(R))), Nat.double(pa.sh(l, 2n+O.Bits.val(i)))),
    pa.val_add(False{} <> O.Bits.shl(l, U), False{} <> O.Bits.shl(l, II), False{}),
    pa.add2(Nat.double(O.Bits.val(O.Bits.shl(l, U))), Nat.double(pa.sh(l, 3n+Nat.double(R))), Nat.double(O.Bits.val(O.Bits.shl(l, II))), Nat.double(pa.sh(l, 2n+O.Bits.val(i))),
      Equal.cong(Nat, Nat, z => Nat.double(z), O.Bits.val(O.Bits.shl(l, U)), pa.sh(l, 3n+Nat.double(R)), Equal.trans(Nat, O.Bits.val(O.Bits.shl(l, U)), pa.sh(l, O.Bits.val(U)), pa.sh(l, 3n+Nat.double(R)), pa.val_shl(l, U), Equal.cong(Nat, Nat, z => pa.sh(l, z), O.Bits.val(U), 3n+Nat.double(R), pa.vu(R)))),
      Equal.cong(Nat, Nat, z => Nat.double(z), O.Bits.val(O.Bits.shl(l, II)), pa.sh(l, 2n+O.Bits.val(i)), Equal.trans(Nat, O.Bits.val(O.Bits.shl(l, II)), pa.sh(l, O.Bits.val(II)), pa.sh(l, 2n+O.Bits.val(i)), pa.val_shl(l, II), Equal.cong(Nat, Nat, z => pa.sh(l, z), O.Bits.val(II), 2n+O.Bits.val(i), pa.vii(i))))))

def pa.vY(+l: Nat, +R: Nat)
  -> {O.Bits.val(O.Bits.add(True{} <> O.Bits.inc(pa.nb(R)), False{} <> O.Bits.shl(l, O.Bits.inc(O.Bits.inc(pa.nb(Nat.double(R))))))) == Nat.add(3n+Nat.double(R), Nat.double(pa.sh(l, 2n+Nat.double(R)))) : Nat}:
  +U = {True{} <> O.Bits.inc(pa.nb(R)) : List<&2, Bool>}
  +PA = O.Bits.inc(O.Bits.inc(pa.nb(Nat.double(R))))
  Equal.trans(Nat, O.Bits.val(O.Bits.add(U, False{} <> O.Bits.shl(l, PA))), Nat.add(O.Bits.val(U), Nat.double(O.Bits.val(O.Bits.shl(l, PA)))), Nat.add(3n+Nat.double(R), Nat.double(pa.sh(l, 2n+Nat.double(R)))),
    pa.val_add(U, False{} <> O.Bits.shl(l, PA), False{}),
    pa.add2(O.Bits.val(U), 3n+Nat.double(R), Nat.double(O.Bits.val(O.Bits.shl(l, PA))), Nat.double(pa.sh(l, 2n+Nat.double(R))),
      pa.vu(R),
      Equal.cong(Nat, Nat, z => Nat.double(z), O.Bits.val(O.Bits.shl(l, PA)), pa.sh(l, 2n+Nat.double(R)), Equal.trans(Nat, O.Bits.val(O.Bits.shl(l, PA)), pa.sh(l, O.Bits.val(PA)), pa.sh(l, 2n+Nat.double(R)), pa.val_shl(l, PA), Equal.cong(Nat, Nat, z => pa.sh(l, z), O.Bits.val(PA), 2n+Nat.double(R), Equal.trans(Nat, O.Bits.val(PA), 2n+O.Bits.val(pa.nb(Nat.double(R))), 2n+Nat.double(R), pa.vii(pa.nb(Nat.double(R))), Equal.cong(Nat, Nat, z => 2n+z, O.Bits.val(pa.nb(Nat.double(R))), Nat.double(R), pa.val_nb(Nat.double(R)))))))))

def pa.old_one.gt(-X: List<&2, Bool>, -Y: List<&2, Bool>, -XX: Nat, +YY: Nat, +k: Nat, ex: {O.Bits.val(X) == XX : Nat}, ey: {O.Bits.val(Y) == YY : Nat}, ei: {XX == Nat.add(YY, 1n+Nat.double(k)) : Nat})
  -> {Nat.is_gt(O.Bits.val(X), O.Bits.val(Y)) == True{} : Bool}:
  %Equal.sym(Nat, O.Bits.val(X), XX, ex) : {Nat.is_gt(_, O.Bits.val(Y)) == True{} : Bool}
  %Equal.sym(Nat, O.Bits.val(Y), YY, ey) : {Nat.is_gt(XX, _) == True{} : Bool}
  %Equal.sym(Nat, XX, Nat.add(YY, 1n+Nat.double(k)), ei) : {Nat.is_gt(_, YY) == True{} : Bool}
  pa.gt_add(YY, Nat.double(k))

# the pair (a0, b0) is more due than a lifted line of the view of R
def pa.old_one(c: O.Node, +R: Nat, g: pa.Good(c, R)) -> {O.more_due(O.Last{}, pa.tb0(R), pa.a0(R), pa.lift(c)) == True{} : Bool}:
  match c:
    case O.Node{+l, +i}:
      (k0, e) = g
      +k = k0
      +U = {True{} <> O.Bits.inc(pa.nb(R)) : List<&2, Bool>}
      +X = O.Bits.add(False{} <> O.Bits.shl(l, U), False{} <> O.Bits.shl(l, O.Bits.inc(O.Bits.inc(i))))
      +Y = O.Bits.add(U, False{} <> O.Bits.shl(l, O.Bits.inc(O.Bits.inc(pa.nb(Nat.double(R))))))
      -XX = Nat.add(Nat.double(pa.sh(l, 3n+Nat.double(R))), Nat.double(pa.sh(l, 2n+O.Bits.val(i))))
      +YY = Nat.add(3n+Nat.double(R), Nat.double(pa.sh(l, 2n+Nat.double(R))))
      pa.gt_val(X, Y, pa.old_one.gt(X, Y, XX, YY, k, pa.vX(l, R, i), pa.vY(l, R), pa.ineq(l, R, O.Bits.val(i), k, e)))

# Pre(t, a, x): the pair from a is more due than x, and x is not a
def pa.Pre(+t: List<&2, Bool>, +a: O.Node, +x: O.Node) -> Type:
  ({O.more_due(O.Last{}, t, a, x) == True{} : Bool} & {O.Node.eq(x, a) == False{} : Bool})

def pa.PreAll(+t: List<&2, Bool>, +a: O.Node, xs: List<&2, O.Node>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +x <> r:
      (pa.Pre(t, a, x) & pa.PreAll(t, a, r))

def pa.eq_lift0(c: O.Node, -ia: List<&2, Bool>) -> {O.Node.eq(pa.lift(c), O.Node{0n, ia}) == False{} : Bool}:
  match c:
    case O.Node{l, i}:
      {==}

def pa.pre_lifts(xs: List<&2, O.Node>, +R: Nat, g: pa.GoodAll(R, xs)) -> pa.PreAll(pa.tb0(R), pa.a0(R), pa.lifts(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case +c <> t:
      (gc, gt) = g
      ((pa.old_one(c, R, gc), pa.eq_lift0(c, pa.nb(Nat.double(R)))), pa.pre_lifts(t, R, gt))

# the best so far, if any, is less due than the pair from a
def pa.OldM(+t: List<&2, Bool>, +a: O.Node, m: Maybe<&2, O.Node>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{c}:
      {O.more_due(O.Last{}, t, a, c) == True{} : Bool}

def pa.oldm_vs(b: Bool, -t: List<&2, Bool>, -a: O.Node, -x: O.Node, -c: O.Node, ox: {O.more_due(O.Last{}, t, a, x) == True{} : Bool}, oc: {O.more_due(O.Last{}, t, a, c) == True{} : Bool})
  -> pa.OldM(t, a, Some{O.best.vs(b, x, c)}):
  match b:
    case True{}:
      ox
    case False{}:
      oc

def pa.oldm_take(cur: Maybe<&2, O.Node>, +t: List<&2, Bool>, -a: O.Node, +x: O.Node, ox: {O.more_due(O.Last{}, t, a, x) == True{} : Bool}, oc: pa.OldM(t, a, cur))
  -> pa.OldM(t, a, O.best.take(O.Last{}, t, x, cur)):
  match cur:
    case None{}:
      ox
    case Some{+c}:
      pa.oldm_vs(O.more_due(O.Last{}, t, x, c), t, a, x, c, ox, oc)

def pa.oldm_pick(ok: Bool, +cur: Maybe<&2, O.Node>, +t: List<&2, Bool>, -a: O.Node, +x: O.Node, ox: {O.more_due(O.Last{}, t, a, x) == True{} : Bool}, oc: pa.OldM(t, a, cur))
  -> pa.OldM(t, a, O.best.pick(ok, O.Last{}, t, x, cur)):
  match ok:
    case False{}:
      oc
    case True{}:
      pa.oldm_take(cur, t, a, x, ox, oc)

def pa.oldm_pair(nxt: Maybe<&2, O.Node>, +cur: Maybe<&2, O.Node>, +t: List<&2, Bool>, -a: O.Node, +x: O.Node, ox: {O.more_due(O.Last{}, t, a, x) == True{} : Bool}, oc: pa.OldM(t, a, cur))
  -> pa.OldM(t, a, O.best.pair(O.Last{}, t, O.All{1n}, x, nxt, cur)):
  match nxt:
    case None{}:
      oc
    case Some{+y}:
      pa.oldm_pick(O.mergeable(O.All{1n}, x, y), cur, t, a, x, ox, oc)

def pa.take_base(cur: Maybe<&2, O.Node>, +t: List<&2, Bool>, +a: O.Node, +b: O.Node, oc: pa.OldM(t, a, cur))
  -> {O.best.go(O.Last{}, t, O.All{1n}, [b], O.best.take(O.Last{}, t, a, cur)) == Some{a} : Maybe<&2, O.Node>}:
  match cur:
    case None{}:
      {==}
    case Some{+c}:
      %Equal.sym(Bool, O.more_due(O.Last{}, t, a, c), True{}, oc) : {O.best.go(O.Last{}, t, O.All{1n}, [b], Some{O.best.vs(_, a, c)}) == Some{a} : Maybe<&2, O.Node>}
      {==}

# best picks a when (a, b) may merge, comes last, and beats every line
# before it
def pa.best_base(xs: List<&2, O.Node>, +cur: Maybe<&2, O.Node>, +t: List<&2, Bool>, +a: O.Node, +b: O.Node, +mab: {O.mergeable(O.All{1n}, a, b) == True{} : Bool}, pre: pa.PreAll(t, a, xs), oc: pa.OldM(t, a, cur))
  -> {O.best.go(O.Last{}, t, O.All{1n}, List.append(&2, O.Node, xs, [a, b]), cur) == Some{a} : Maybe<&2, O.Node>}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, O.mergeable(O.All{1n}, a, b), True{}, mab) : {O.best.go(O.Last{}, t, O.All{1n}, [b], O.best.pick(_, O.Last{}, t, a, cur)) == Some{a} : Maybe<&2, O.Node>}
      pa.take_base(cur, t, a, b, oc)
    case +x <> +r:
      (px, pr) = pre
      (ox, ex) = px
      pa.best_base(r, O.best.pair(O.Last{}, t, O.All{1n}, x, List.head(&2, O.Node, List.append(&2, O.Node, r, [a, b])), cur), t, a, b, mab, pr, pa.oldm_pair(List.head(&2, O.Node, List.append(&2, O.Node, r, [a, b])), cur, t, a, x, ox, oc))

def pa.node_eq_self(n: O.Node) -> {O.Node.eq(n, n) == True{} : Bool}:
  match n:
    case O.Node{+l, +i}:
      %Equal.sym(Bool, O.Bits.same(i, i), True{}, pa.same_val(i, i, {==})) : {Bool.and(Nat.is_eq(l, l), _) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(l, l), EQ{}, pa.cmp_self(l)) : {Bool.and(Cmp.is_eq(_), True{}) == True{} : Bool}
      {==}

def pa.mhere_base(xs: List<&2, O.Node>, +x: O.Node, +a: O.Node, +b: O.Node, ex: {O.Node.eq(x, a) == False{} : Bool})
  -> {O.merge.here(O.All{1n}, a, x, List.append(&2, O.Node, xs, [a, b]), List.append(&2, O.Node, xs, [O.Node.parent(a)])) == x <> List.append(&2, O.Node, xs, [O.Node.parent(a)]) : List<&2, O.Node>}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, O.Node.eq(x, a), False{}, ex) : {O.merge.pick(Bool.and(_, O.mergeable(O.All{1n}, x, a)), x, a, [b], [O.Node.parent(a)]) == [x, O.Node.parent(a)] : List<&2, O.Node>}
      {==}
    case +y <> +r:
      %Equal.sym(Bool, O.Node.eq(x, a), False{}, ex) : {O.merge.pick(Bool.and(_, O.mergeable(O.All{1n}, x, y)), x, y, List.append(&2, O.Node, r, [a, b]), y <> List.append(&2, O.Node, r, [O.Node.parent(a)])) == x <> y <> List.append(&2, O.Node, r, [O.Node.parent(a)]) : List<&2, O.Node>}
      {==}

# the merge of a replaces (a, b) by their parent
def pa.merge_base(xs: List<&2, O.Node>, +a: O.Node, +b: O.Node, +mab: {O.mergeable(O.All{1n}, a, b) == True{} : Bool}, -t: List<&2, Bool>, pre: pa.PreAll(t, a, xs))
  -> {O.merge(O.All{1n}, List.append(&2, O.Node, xs, [a, b]), a) == List.append(&2, O.Node, xs, [O.Node.parent(a)]) : List<&2, O.Node>}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, O.Node.eq(a, a), True{}, pa.node_eq_self(a)) : {O.merge.pick(Bool.and(_, O.mergeable(O.All{1n}, a, b)), a, b, Nil{}, O.merge(O.All{1n}, [b], a)) == [O.Node.parent(a)] : List<&2, O.Node>}
      %Equal.sym(Bool, O.mergeable(O.All{1n}, a, b), True{}, mab) : {O.merge.pick(Bool.and(True{}, _), a, b, Nil{}, O.merge(O.All{1n}, [b], a)) == [O.Node.parent(a)] : List<&2, O.Node>}
      {==}
    case +x <> +r:
      (px, pr) = pre
      (ox, ex) = px
      %Equal.sym(List<&2, O.Node>, O.merge(O.All{1n}, List.append(&2, O.Node, r, [a, b]), a), List.append(&2, O.Node, r, [O.Node.parent(a)]), pa.merge_base(r, a, b, mab, t, pr)) : {O.merge.here(O.All{1n}, a, x, List.append(&2, O.Node, r, [a, b]), _) == x <> List.append(&2, O.Node, r, [O.Node.parent(a)]) : List<&2, O.Node>}
      pa.mhere_base(r, x, a, b, ex)

def pa.mab(+R: Nat) -> {O.mergeable(O.All{1n}, pa.a0(R), pa.b0(R)) == True{} : Bool}:
  %Equal.sym(Bool, O.Bits.low(pa.nb(Nat.double(R))), False{}, pa.low_even(R)) : {Bool.and(Bool.and(Bool.not(_), O.Bits.eq(O.Bits.up(pa.nb(Nat.double(R))), pa.nb(R))), True{}) == True{} : Bool}
  %Equal.sym(List<&2, Bool>, O.Bits.up(pa.nb(Nat.double(R))), pa.nb(R), pa.up_even(R)) : {Bool.and(O.Bits.eq(_, pa.nb(R)), True{}) == True{} : Bool}
  %Equal.sym(Bool, O.Bits.eq(pa.nb(R), pa.nb(R)), True{}, pa.bits_eq_self(pa.nb(R))) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

# One step
# --------

def pa.fit_none(f: Nat, -t: List<&2, Bool>, -bud: Nat, -w: List<&2, O.Node>) -> {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(f, None{}, O.Last{}, t, bud, 0n, O.All{1n}, w)) == w : List<&2, O.Node>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# a fit that merges a, then fits: one merge
def pa.base_fit(+f: Nat, +y: List<&2, O.Node>, +a: O.Node, +w: List<&2, O.Node>, +t: List<&2, Bool>, +bud: Nat,
  hc: {O.choose(O.Last{}, t, bud, 0n, O.All{1n}, y) == Some{a} : Maybe<&2, O.Node>},
  hm: {O.merge(O.All{1n}, y, a) == w : List<&2, O.Node>},
  hn: {O.choose(O.Last{}, t, bud, 0n, O.All{1n}, w) == None{} : Maybe<&2, O.Node>})
  -> {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, O.choose(O.Last{}, t, bud, 0n, O.All{1n}, y), O.Last{}, t, bud, 0n, O.All{1n}, y)) == w : List<&2, O.Node>}:
  %Equal.sym(Maybe<&2, O.Node>, O.choose(O.Last{}, t, bud, 0n, O.All{1n}, y), Some{a}, hc) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, _, O.Last{}, t, bud, 0n, O.All{1n}, y)) == w : List<&2, O.Node>}
  %pa.snd_cons(O.Node.parent(a), O.fit.go(f, O.choose(O.Last{}, t, bud, 0n, O.All{1n}, O.merge(O.All{1n}, y, a)), O.Last{}, t, bud, 0n, O.All{1n}, O.merge(O.All{1n}, y, a))) : {_ == w : List<&2, O.Node>}
  %Equal.sym(List<&2, O.Node>, O.merge(O.All{1n}, y, a), w, hm) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(f, O.choose(O.Last{}, t, bud, 0n, O.All{1n}, _), O.Last{}, t, bud, 0n, O.All{1n}, _)) == w : List<&2, O.Node>}
  %Equal.sym(Maybe<&2, O.Node>, O.choose(O.Last{}, t, bud, 0n, O.All{1n}, w), None{}, hn) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(f, _, O.Last{}, t, bud, 0n, O.All{1n}, w)) == w : List<&2, O.Node>}
  pa.fit_none(f, t, bud, w)

def pa.app_ab(xs: List<&2, O.Node>, +a: O.Node, +b: O.Node) -> {List.append(&2, O.Node, List.append(&2, O.Node, xs, [a]), [b]) == List.append(&2, O.Node, xs, [a, b]) : List<&2, O.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, O.Node>, List<&2, O.Node>, z => h <> z, List.append(&2, O.Node, List.append(&2, O.Node, t, [a]), [b]), List.append(&2, O.Node, t, [a, b]), pa.app_ab(t, a, b))

def pa.lifts_app1(xs: List<&2, O.Node>, +y: O.Node) -> {pa.lifts(List.append(&2, O.Node, xs, [y])) == List.append(&2, O.Node, pa.lifts(xs), [pa.lift(y)]) : List<&2, O.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, O.Node>, List<&2, O.Node>, z => pa.lift(h) <> z, pa.lifts(List.append(&2, O.Node, t, [y])), List.append(&2, O.Node, pa.lifts(t), [pa.lift(y)]), pa.lifts_app1(t, y))

# T + 1, the view with message T's line, and the budget push gives
def pa.T2(+ds: List<&2, Bool>) -> List<&2, Bool>:
  O.Bits.inc(pa.nb(pa.B(ds)))

def pa.V(+ds: List<&2, Bool>) -> List<&2, O.Node>:
  List.append(&2, O.Node, pa.GV(ds), [O.Node.leaf(pa.nb(pa.B(ds)))])

def pa.bud(+ds: List<&2, Bool>) -> Nat:
  List.length(&2, Bool, pa.inc(ds))

# the fit of one step (with any fuel above 0) is the view of T + 1
def pa.FT(+ds: List<&2, Bool>, +f: Nat) -> Type:
  {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, O.choose(O.Last{}, pa.T2(ds), pa.bud(ds), 0n, O.All{1n}, pa.V(ds)), O.Last{}, pa.T2(ds), pa.bud(ds), 0n, O.All{1n}, pa.V(ds))) == pa.GV(pa.inc(ds)) : List<&2, O.Node>}

def pa.hc_base(+r: List<&2, Bool>)
  -> {O.choose(O.Last{}, pa.tb0(pa.B(r)), 1n+List.length(&2, Bool, r), 0n, O.All{1n}, List.append(&2, O.Node, pa.lifts(pa.GV(r)), [pa.a0(pa.B(r)), pa.b0(pa.B(r))])) == Some{pa.a0(pa.B(r))} : Maybe<&2, O.Node>}:
  +R = pa.B(r)
  +y = List.append(&2, O.Node, pa.lifts(pa.GV(r)), [pa.a0(R), pa.b0(R)])
  %Equal.sym(Nat, pa.vs(y), 2n+List.length(&2, Bool, r), pa.size_hi(r, [pa.a0(R), pa.b0(R)])) : {O.choose.if(Nat.is_gt(_, 1n+List.length(&2, Bool, r)), O.Last{}, pa.tb0(R), O.All{1n}, y) == Some{pa.a0(R)} : Maybe<&2, O.Node>}
  %Equal.sym(Bool, Nat.is_gt(1n+List.length(&2, Bool, r), List.length(&2, Bool, r)), True{}, pa.gt_succ(List.length(&2, Bool, r))) : {O.choose.if(_, O.Last{}, pa.tb0(R), O.All{1n}, y) == Some{pa.a0(R)} : Maybe<&2, O.Node>}
  pa.best_base(pa.lifts(pa.GV(r)), None{}, pa.tb0(R), pa.a0(R), pa.b0(R), pa.mab(R), pa.pre_lifts(pa.GV(r), R, pa.good_gv(r)), Unit{})

def pa.hm_base(+r: List<&2, Bool>)
  -> {O.merge(O.All{1n}, List.append(&2, O.Node, pa.lifts(pa.GV(r)), [pa.a0(pa.B(r)), pa.b0(pa.B(r))]), pa.a0(pa.B(r))) == pa.GV(True{} <> r) : List<&2, O.Node>}:
  +R = pa.B(r)
  Equal.trans(List<&2, O.Node>, O.merge(O.All{1n}, List.append(&2, O.Node, pa.lifts(pa.GV(r)), [pa.a0(R), pa.b0(R)]), pa.a0(R)), List.append(&2, O.Node, pa.lifts(pa.GV(r)), [O.Node.parent(pa.a0(R))]), pa.GV(True{} <> r),
    pa.merge_base(pa.lifts(pa.GV(r)), pa.a0(R), pa.b0(R), pa.mab(R), pa.tb0(R), pa.pre_lifts(pa.GV(r), R, pa.good_gv(r))),
    Equal.cong(List<&2, Bool>, List<&2, O.Node>, z => List.append(&2, O.Node, pa.lifts(pa.GV(r)), [O.Node{1n, z}]), O.Bits.up(pa.nb(Nat.double(R))), pa.nb(R), pa.up_even(R)))

def pa.hn_base(+r: List<&2, Bool>)
  -> {O.choose(O.Last{}, pa.tb0(pa.B(r)), 1n+List.length(&2, Bool, r), 0n, O.All{1n}, pa.GV(True{} <> r)) == None{} : Maybe<&2, O.Node>}:
  +R = pa.B(r)
  %Equal.sym(Nat, pa.vs(pa.GV(True{} <> r)), 1n+List.length(&2, Bool, r), pa.size_hi(r, [O.Node{1n, pa.nb(R)}])) : {O.choose.if(Nat.is_gt(_, 1n+List.length(&2, Bool, r)), O.Last{}, pa.tb0(R), O.All{1n}, pa.GV(True{} <> r)) == None{} : Maybe<&2, O.Node>}
  %Equal.sym(Bool, Nat.is_gt(1n+List.length(&2, Bool, r), 1n+List.length(&2, Bool, r)), False{}, pa.gt_self(1n+List.length(&2, Bool, r))) : {O.choose.if(_, O.Last{}, pa.tb0(R), O.All{1n}, pa.GV(True{} <> r)) == None{} : Maybe<&2, O.Node>}
  {==}

# lowest digit 0: the new line merges with line 0
def pa.F_base(+r: List<&2, Bool>, +f: Nat) -> pa.FT(False{} <> r, f):
  +R = pa.B(r)
  +X = pa.lifts(pa.GV(r))
  +n = {1n+List.length(&2, Bool, r) : Nat}
  %Equal.sym(List<&2, Bool>, pa.nb(1n+Nat.double(R)), True{} <> pa.nb(R), pa.nb_odd(R)) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, O.choose(O.Last{}, O.Bits.inc(_), n, 0n, O.All{1n}, List.append(&2, O.Node, List.append(&2, O.Node, X, [pa.a0(R)]), [O.Node{0n, _}])), O.Last{}, O.Bits.inc(_), n, 0n, O.All{1n}, List.append(&2, O.Node, List.append(&2, O.Node, X, [pa.a0(R)]), [O.Node{0n, _}]))) == pa.GV(True{} <> r) : List<&2, O.Node>}
  %Equal.sym(List<&2, O.Node>, List.append(&2, O.Node, List.append(&2, O.Node, X, [pa.a0(R)]), [pa.b0(R)]), List.append(&2, O.Node, X, [pa.a0(R), pa.b0(R)]), pa.app_ab(X, pa.a0(R), pa.b0(R))) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, O.choose(O.Last{}, pa.tb0(R), n, 0n, O.All{1n}, _), O.Last{}, pa.tb0(R), n, 0n, O.All{1n}, _)) == pa.GV(True{} <> r) : List<&2, O.Node>}
  pa.base_fit(f, List.append(&2, O.Node, X, [pa.a0(R), pa.b0(R)]), pa.a0(R), pa.GV(True{} <> r), pa.tb0(R), n, pa.hc_base(r), pa.hm_base(r), pa.hn_base(r))

# lowest digit 1: the step is the lifted step of the higher digits
def pa.F_lift(+r: List<&2, Bool>, +f: Nat, ih: pa.FT(r, f)) -> pa.FT(True{} <> r, f):
  +R = pa.B(r)
  +iz = pa.nb(2n+Nat.double(R))
  +t = pa.T2(True{} <> r)
  +t0 = pa.T2(r)
  +b = pa.bud(r)
  +c0 = O.choose(O.Last{}, t0, b, 0n, O.All{1n}, pa.V(r))
  +hu = Equal.sym(List<&2, Bool>, O.Bits.inc(O.Bits.inc(pa.nb(2n+Nat.double(R)))), O.Bits.inc(O.Bits.inc(False{} <> pa.nb(1n+R))), Equal.cong(List<&2, Bool>, List<&2, Bool>, z => O.Bits.inc(O.Bits.inc(z)), pa.nb(2n+Nat.double(R)), False{} <> pa.nb(1n+R), pa.nb_even(R)))
  %Equal.cong(List<&2, O.Node>, List<&2, O.Node>, w => List.append(&2, O.Node, w, [O.Node{0n, iz}]), pa.lifts(List.append(&2, O.Node, pa.GV(r), [O.Node{0n, pa.nb(R)}])), List.append(&2, O.Node, pa.lifts(pa.GV(r)), [pa.lift(O.Node{0n, pa.nb(R)})]), pa.lifts_app1(pa.GV(r), O.Node{0n, pa.nb(R)})) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, O.choose(O.Last{}, t, 1n+b, 0n, O.All{1n}, _), O.Last{}, t, 1n+b, 0n, O.All{1n}, _)) == pa.GV(False{} <> pa.inc(r)) : List<&2, O.Node>}
  %Equal.sym(Maybe<&2, O.Node>, O.choose(O.Last{}, t, 1n+b, 0n, O.All{1n}, pa.up(pa.V(r), O.Node{0n, iz})), pa.liftm(c0), pa.choose_lift(pa.V(r), b, iz, t, t0, hu)) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, _, O.Last{}, t, 1n+b, 0n, O.All{1n}, pa.up(pa.V(r), O.Node{0n, iz}))) == pa.GV(False{} <> pa.inc(r)) : List<&2, O.Node>}
  -S0 = Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, c0, O.Last{}, t0, b, 0n, O.All{1n}, pa.V(r)))
  Equal.trans(List<&2, O.Node>, Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(1n+f, pa.liftm(c0), O.Last{}, t, 1n+b, 0n, O.All{1n}, pa.up(pa.V(r), O.Node{0n, iz}))), pa.up(S0, O.Node{0n, iz}), pa.GV(False{} <> pa.inc(r)),
    pa.fit_lift(1n+f, c0, pa.V(r), b, iz, t, t0, hu),
    Equal.trans(List<&2, O.Node>, pa.up(S0, O.Node{0n, iz}), pa.up(pa.GV(pa.inc(r)), O.Node{0n, iz}), pa.GV(False{} <> pa.inc(r)),
      Equal.cong(List<&2, O.Node>, List<&2, O.Node>, w => pa.up(w, O.Node{0n, iz}), S0, pa.GV(pa.inc(r)), ih),
      Equal.cong(Nat, List<&2, O.Node>, w => List.append(&2, O.Node, pa.lifts(pa.GV(pa.inc(r))), [O.Node{0n, pa.nb(Nat.double(w))}]), 1n+R, pa.B(pa.inc(r)), Equal.sym(Nat, pa.B(pa.inc(r)), 1n+R, pa.B_inc(r)))))

def pa.F(ds: List<&2, Bool>, +f: Nat) -> pa.FT(ds, f):
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          pa.F_base(r, f)
        case True{}:
          pa.F_lift(r, f, pa.F(r, f))

# the view push's budget leaves after message T is the view of T + 1
def pa.step(+ds: List<&2, Bool>) -> {O.fit.view(O.Last{}, pa.T2(ds), List.length(&2, O.Entry, pa.GE(pa.inc(ds), 0n)), 0n, O.All{1n}, pa.V(ds)) == pa.GV(pa.inc(ds)) : List<&2, O.Node>}:
  %Equal.sym(Nat, List.length(&2, O.Entry, pa.GE(pa.inc(ds), 0n)), pa.bud(ds), pa.len_GE(pa.inc(ds), 0n)) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(List.length(&2, O.Node, pa.V(ds)), O.choose(O.Last{}, pa.T2(ds), _, 0n, O.All{1n}, pa.V(ds)), O.Last{}, pa.T2(ds), _, 0n, O.All{1n}, pa.V(ds))) == pa.GV(pa.inc(ds)) : List<&2, O.Node>}
  %Equal.sym(Nat, List.length(&2, O.Node, pa.V(ds)), 1n+List.length(&2, O.Node, pa.GV(ds)), pa.len_app1(pa.GV(ds), O.Node.leaf(pa.nb(pa.B(ds))))) : {Pair.snd(List<&2, O.Node>, List<&2, O.Node>, O.fit.go(_, O.choose(O.Last{}, pa.T2(ds), pa.bud(ds), 0n, O.All{1n}, pa.V(ds)), O.Last{}, pa.T2(ds), pa.bud(ds), 0n, O.All{1n}, pa.V(ds))) == pa.GV(pa.inc(ds)) : List<&2, O.Node>}
  pa.F(ds, List.length(&2, O.Node, pa.GV(ds)))

# The law
# -------

def pa.agree(n: Nat, +ds: List<&2, Bool>) -> {O.agree.go(n, O.Last{}, pa.nb(pa.B(ds)), pa.GE(ds, 0n), pa.GV(ds)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +es2 = pa.GE(pa.inc(ds), 0n)
      +v2 = pa.GV(pa.inc(ds))
      %Equal.sym(List<&2, O.Entry>, O.push(pa.GE(ds, 0n), pa.nb(pa.B(ds))), es2, pa.push_ge(ds, 0n)) : {Bool.and(O.same_lines(O.fit.view(O.Last{}, pa.T2(ds), List.length(&2, O.Entry, _), 0n, O.All{1n}, pa.V(ds)), _), O.agree.go(p, O.Last{}, pa.T2(ds), _, O.fit.view(O.Last{}, pa.T2(ds), List.length(&2, O.Entry, _), 0n, O.All{1n}, pa.V(ds)))) == True{} : Bool}
      %Equal.sym(List<&2, O.Node>, O.fit.view(O.Last{}, pa.T2(ds), List.length(&2, O.Entry, es2), 0n, O.All{1n}, pa.V(ds)), v2, pa.step(ds)) : {Bool.and(O.same_lines(_, es2), O.agree.go(p, O.Last{}, pa.T2(ds), es2, _)) == True{} : Bool}
      %pa.B_inc(ds) : {Bool.and(O.same_lines(v2, es2), O.agree.go(p, O.Last{}, pa.nb(_), es2, v2)) == True{} : Bool}
      %Equal.sym(Bool, O.same_lines(v2, es2), True{}, pa.same_lines(pa.inc(ds))) : {Bool.and(_, O.agree.go(p, O.Last{}, pa.nb(pa.B(pa.inc(ds))), es2, v2)) == True{} : Bool}
      pa.agree(p, pa.inc(ds))

def push_agrees_always(n: Nat) -> {O.agree(O.Last{}, n) == True{} : Bool}:
  pa.agree(n, Nil{})

def Optchat.push_agrees_always(n):
  push_agrees_always(n)
