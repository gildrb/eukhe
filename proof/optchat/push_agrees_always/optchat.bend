# eukhe: lemmas of the proof of LAW push_agrees_always: optchat

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/fit.bend as OFit
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/push.bend as OPush
import ../../base/nat/add.bend as LNatAdd
import ../../base/nat/misc.bend as LNatMisc
import ../base.bend as LA
import ./list.bend as LLList
import ./nat.bend as LLNat
import ./pair.bend as LLPair

# Bits and their values
# ---------------------

def pa.val_inc(x: List<&2, Bool>) -> {OBits.Bits.val(OBits.Bits.inc(x)) == 1n+OBits.Bits.val(x) : Nat}:
  match x:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case False{}:
          {==}
        case True{}:
          Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(OBits.Bits.inc(t)), 1n+OBits.Bits.val(t), pa.val_inc(t))

def pa.val_shl(l: Nat, +x: List<&2, Bool>) -> {OBits.Bits.val(OBits.Bits.shl(l, x)) == LLNat.pa.sh(l, OBits.Bits.val(x)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(OBits.Bits.shl(p, x)), LLNat.pa.sh(p, OBits.Bits.val(x)), pa.val_shl(p, x))

# a full adder: the sum bit, then twice the carry
def pa.fa(x: Bool, y: Bool, c: Bool, -S: Nat) -> {OBits.bit(Bool.xor(Bool.xor(x, y), c), Nat.double(OBits.bit(Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))), S))) == OBits.bit(c, OBits.bit(x, OBits.bit(y, Nat.double(S)))) : Nat}:
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
  ih: {L == OBits.bit(Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))), Nat.add(A, B)) : Nat})
  -> {OBits.bit(Bool.xor(Bool.xor(x, y), c), Nat.double(L)) == OBits.bit(c, Nat.add(OBits.bit(x, Nat.double(A)), OBits.bit(y, Nat.double(B)))) : Nat}:
  %Equal.sym(Nat, L, OBits.bit(Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))), Nat.add(A, B)), ih) : {OBits.bit(Bool.xor(Bool.xor(x, y), c), Nat.double(_)) == OBits.bit(c, Nat.add(OBits.bit(x, Nat.double(A)), OBits.bit(y, Nat.double(B)))) : Nat}
  %Equal.sym(Nat, Nat.add(OBits.bit(x, Nat.double(A)), OBits.bit(y, Nat.double(B))), OBits.bit(x, OBits.bit(y, Nat.add(Nat.double(A), Nat.double(B)))), LLNat.pa.add_bits(x, y, Nat.double(A), Nat.double(B))) : {OBits.bit(Bool.xor(Bool.xor(x, y), c), Nat.double(OBits.bit(Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))), Nat.add(A, B)))) == OBits.bit(c, _) : Nat}
  %LLNat.pa.double_add(A, B) : {OBits.bit(Bool.xor(Bool.xor(x, y), c), Nat.double(OBits.bit(Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))), Nat.add(A, B)))) == OBits.bit(c, OBits.bit(x, OBits.bit(y, _))) : Nat}
  pa.fa(x, y, c, Nat.add(A, B))

# the value of x + y + c
def pa.val_add(xs: List<&2, Bool>, ys: List<&2, Bool>, +c: Bool) -> {OBits.Bits.val(OBits.Bits.add.go(xs, ys, c)) == OBits.bit(c, Nat.add(OBits.Bits.val(xs), OBits.Bits.val(ys))) : Nat}:
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
          Equal.sym(Nat, Nat.add(OBits.Bits.val(x <> xt), 0n), OBits.Bits.val(x <> xt), LNatAdd.pa.add_zero(OBits.Bits.val(x <> xt)))
        case True{}:
          Equal.trans(Nat, OBits.Bits.val(OBits.Bits.inc(x <> xt)), 1n+OBits.Bits.val(x <> xt), 1n+Nat.add(OBits.Bits.val(x <> xt), 0n), pa.val_inc(x <> xt), LNatMisc.pa.succ(OBits.Bits.val(x <> xt), Nat.add(OBits.Bits.val(x <> xt), 0n), Equal.sym(Nat, Nat.add(OBits.Bits.val(x <> xt), 0n), OBits.Bits.val(x <> xt), LNatAdd.pa.add_zero(OBits.Bits.val(x <> xt)))))
    case +x <> +xt +y <> +yt:
      pa.val_add.cons(x, y, c, OBits.Bits.val(xt), OBits.Bits.val(yt), OBits.Bits.val(OBits.Bits.add.go(xt, yt, Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))))), pa.val_add(xt, yt, Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y)))))

def pa.gt_val(+xs: List<&2, Bool>, +ys: List<&2, Bool>, e: {Nat.is_gt(OBits.Bits.val(xs), OBits.Bits.val(ys)) == True{} : Bool}) -> {OBits.Bits.gt(xs, ys) == True{} : Bool}:
  %Equal.sym(Cmp, OBits.Bits.cmp(xs, ys), Nat.cmp(OBits.Bits.val(xs), OBits.Bits.val(ys)), LA.pa.cmp_val(xs, ys)) : {Cmp.is_gt(_) == True{} : Bool}
  e

def pa.same_val(+xs: List<&2, Bool>, +ys: List<&2, Bool>, e: {OBits.Bits.val(xs) == OBits.Bits.val(ys) : Nat}) -> {OBits.Bits.same(xs, ys) == True{} : Bool}:
  %Equal.sym(Cmp, OBits.Bits.cmp(xs, ys), Nat.cmp(OBits.Bits.val(xs), OBits.Bits.val(ys)), LA.pa.cmp_val(xs, ys)) : {Cmp.is_eq(_) == True{} : Bool}
  %e : {Cmp.is_eq(Nat.cmp(OBits.Bits.val(xs), _)) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(OBits.Bits.val(xs), OBits.Bits.val(xs)), EQ{}, LLNat.pa.cmp_self(OBits.Bits.val(xs))) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def pa.val_nb(+n: Nat) -> {OBits.Bits.val(LLList.pa.nb(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, OBits.Bits.val(OBits.Bits.inc(LLList.pa.nb(p))), 1n+OBits.Bits.val(LLList.pa.nb(p)), 1n+p, pa.val_inc(LLList.pa.nb(p)), LNatMisc.pa.succ(OBits.Bits.val(LLList.pa.nb(p)), p, pa.val_nb(p)))

def pa.low_even(+r: Nat) -> {OBits.Bits.low(LLList.pa.nb(Nat.double(r))) == False{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, Bool>, LLList.pa.nb(2n+Nat.double(p)), False{} <> LLList.pa.nb(1n+p), LLList.pa.nb_even(p)) : {OBits.Bits.low(_) == False{} : Bool}
      {==}

def pa.up_even(+r: Nat) -> {OBits.Bits.up(LLList.pa.nb(Nat.double(r))) == LLList.pa.nb(r) : List<&2, Bool>}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, Bool>, LLList.pa.nb(2n+Nat.double(p)), False{} <> LLList.pa.nb(1n+p), LLList.pa.nb_even(p)) : {OBits.Bits.up(_) == LLList.pa.nb(1n+p) : List<&2, Bool>}
      {==}

def pa.bits_eq_self(x: List<&2, Bool>) -> {OBits.Bits.eq(x, x) == True{} : Bool}:
  match x:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case False{}:
          pa.bits_eq_self(t)
        case True{}:
          pa.bits_eq_self(t)

# the view (oldest first): the view of the higher digits one level up,
# then the line of digit 0, of level d_0
def pa.lift(n: ONode.Node) -> ONode.Node:
  match n:
    case ONode.Node{l, i}:
      ONode.Node{1n+l, i}

def pa.lifts(v: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match v:
    case Nil{}:
      Nil{}
    case h <> t:
      pa.lift(h) <> pa.lifts(t)

def pa.line(d: Bool, +r: Nat) -> ONode.Node:
  match d:
    case False{}:
      ONode.Node{0n, LLList.pa.nb(Nat.double(r))}
    case True{}:
      ONode.Node{1n, LLList.pa.nb(r)}

def pa.GV(ds: List<&2, Bool>) -> List<&2, ONode.Node>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> +r:
      List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), [pa.line(d, LLNat.pa.B(r))])

# Push is the counter
# -------------------

def pa.push_ge(ds: List<&2, Bool>, +j: Nat) -> {OPush.push(LLList.pa.GE(ds, j), LLList.pa.nb(LLNat.pa.sh(j, LLNat.pa.B(ds)))) == LLList.pa.GE(LLList.pa.inc(ds), j) : List<&2, OPush.Entry>}:
  match ds:
    case Nil{}:
      %Equal.sym(Nat, LLNat.pa.sh(j, 0n), 0n, LLNat.pa.sh_zero(j)) : {[OPush.Entry{0n, 0n, LLList.pa.nb(_)}] == [OPush.Entry{0n, 0n, LLList.pa.nb(Nat.double(_))}] : List<&2, OPush.Entry>}
      {==}
    case d <> +r:
      match d:
        case False{}:
          {==}
        case True{}:
          %pa.push_ge(r, 1n+j) : {OPush.Entry{0n, 0n, LLList.pa.nb(LLNat.pa.sh(j, 2n+Nat.double(LLNat.pa.B(r))))} <> OPush.push(LLList.pa.GE(r, 1n+j), LLList.pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(r)))) == OPush.Entry{0n, 0n, LLList.pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(LLList.pa.inc(r))))} <> _ : List<&2, OPush.Entry>}
          %LLList.pa.B_inc(r) : {OPush.Entry{0n, 0n, LLList.pa.nb(LLNat.pa.sh(j, Nat.double(_)))} <> OPush.push(LLList.pa.GE(r, 1n+j), LLList.pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(r)))) == OPush.Entry{0n, 0n, LLList.pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(LLList.pa.inc(r))))} <> OPush.push(LLList.pa.GE(r, 1n+j), LLList.pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(r)))) : List<&2, OPush.Entry>}
          %LLNat.pa.sh_double(j, LLNat.pa.B(LLList.pa.inc(r))) : {OPush.Entry{0n, 0n, LLList.pa.nb(LLNat.pa.sh(j, Nat.double(LLNat.pa.B(LLList.pa.inc(r)))))} <> OPush.push(LLList.pa.GE(r, 1n+j), LLList.pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(r)))) == OPush.Entry{0n, 0n, LLList.pa.nb(_)} <> OPush.push(LLList.pa.GE(r, 1n+j), LLList.pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(r)))) : List<&2, OPush.Entry>}
          {==}

def pa.same_vals(xs: List<&2, List<&2, Bool>>, ys: List<&2, List<&2, Bool>>, +e: {LLList.pa.vals(xs) == LLList.pa.vals(ys) : List<&2, Nat>}) -> {OPush.Bitss.same(xs, ys) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      LLList.pa.nil_cons({False{} == True{} : Bool}, OBits.Bits.val(y), LLList.pa.vals(yt), e)
    case +x <> +xt Nil{}:
      LLList.pa.nil_cons({False{} == True{} : Bool}, OBits.Bits.val(x), LLList.pa.vals(xt), Equal.sym(List<&2, Nat>, OBits.Bits.val(x) <> LLList.pa.vals(xt), Nil{}, e))
    case +x <> +xt +y <> +yt:
      %Equal.sym(Bool, OBits.Bits.same(x, y), True{}, pa.same_val(x, y, Equal.cong(List<&2, Nat>, Nat, z => LLNat.pa.hd(z), OBits.Bits.val(x) <> LLList.pa.vals(xt), OBits.Bits.val(y) <> LLList.pa.vals(yt), e))) : {Bool.and(_, OPush.Bitss.same(xt, yt)) == True{} : Bool}
      pa.same_vals(xt, yt, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LLList.pa.tl(z), OBits.Bits.val(x) <> LLList.pa.vals(xt), OBits.Bits.val(y) <> LLList.pa.vals(yt), e))

def pa.SG(ds: List<&2, Bool>) -> List<&2, Nat>:
  LLList.pa.vals(OPush.starts(pa.GV(ds)))

# val(nb(2x)) = 2·val(nb(x))
def pa.val_nb2(+x: Nat) -> {OBits.Bits.val(LLList.pa.nb(Nat.double(x))) == Nat.double(OBits.Bits.val(LLList.pa.nb(x))) : Nat}:
  Equal.trans(Nat, OBits.Bits.val(LLList.pa.nb(Nat.double(x))), Nat.double(x), Nat.double(OBits.Bits.val(LLList.pa.nb(x))), pa.val_nb(Nat.double(x)), Equal.cong(Nat, Nat, z => Nat.double(z), x, OBits.Bits.val(LLList.pa.nb(x)), Equal.sym(Nat, OBits.Bits.val(LLList.pa.nb(x)), x, pa.val_nb(x))))

def pa.vs_app(xs: List<&2, ONode.Node>, +y: ONode.Node) -> {LLList.pa.vals(OPush.starts(List.append(&2, ONode.Node, xs, [y]))) == List.append(&2, Nat, LLList.pa.vals(OPush.starts(xs)), [OBits.Bits.val(OFit.pair_start(y))]) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => OBits.Bits.val(OFit.pair_start(h)) <> z, LLList.pa.vals(OPush.starts(List.append(&2, ONode.Node, t, [y]))), List.append(&2, Nat, LLList.pa.vals(OPush.starts(t)), [OBits.Bits.val(OFit.pair_start(y))]), pa.vs_app(t, y))

def pa.vs_lifts(xs: List<&2, ONode.Node>) -> {LLList.pa.vals(OPush.starts(pa.lifts(xs))) == LLList.pa.dbls(LLList.pa.vals(OPush.starts(xs))) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case ONode.Node{+l, +i}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Nat.double(OBits.Bits.val(OBits.Bits.shl(l, i))) <> z, LLList.pa.vals(OPush.starts(pa.lifts(t))), LLList.pa.dbls(LLList.pa.vals(OPush.starts(t))), pa.vs_lifts(t))

# one level up, every state doubles
def pa.vst(ds: List<&2, Bool>, +j: Nat) -> {LLList.pa.SE(ds, 1n+j) == LLList.pa.dbls(LLList.pa.SE(ds, j)) : List<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          LLList.pa.cons2(OBits.Bits.val(LLList.pa.nb(Nat.double(LLNat.pa.sh(1n+j, LLNat.pa.B(r))))), Nat.double(OBits.Bits.val(LLList.pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(r))))), LLList.pa.SE(r, 2n+j), LLList.pa.dbls(LLList.pa.SE(r, 1n+j)), pa.val_nb2(LLNat.pa.sh(1n+j, LLNat.pa.B(r))), pa.vst(r, 1n+j))
        case True{}:
          LLList.pa.cons2(OBits.Bits.val(LLList.pa.nb(Nat.double(LLNat.pa.sh(1n+j, LLNat.pa.B(r))))), Nat.double(OBits.Bits.val(LLList.pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(r))))), LLList.pa.SE(r, 2n+j), LLList.pa.dbls(LLList.pa.SE(r, 1n+j)), pa.val_nb2(LLNat.pa.sh(1n+j, LLNat.pa.B(r))), pa.vst(r, 1n+j))

# line 0 starts at 2·B(r)
def pa.vlast(d: Bool, +r: Nat) -> {OBits.Bits.val(OFit.pair_start(pa.line(d, r))) == Nat.double(r) : Nat}:
  match d:
    case False{}:
      pa.val_nb(Nat.double(r))
    case True{}:
      Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(LLList.pa.nb(r)), r, pa.val_nb(r))

def pa.sv_l(+d: Bool, +r: List<&2, Bool>, ih: {pa.SG(r) == LLList.pa.rev(LLList.pa.SE(r, 0n)) : List<&2, Nat>}) -> {pa.SG(d <> r) == List.append(&2, Nat, LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), [Nat.double(LLNat.pa.B(r))]) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, pa.SG(d <> r), List.append(&2, Nat, LLList.pa.vals(OPush.starts(pa.lifts(pa.GV(r)))), [OBits.Bits.val(OFit.pair_start(pa.line(d, LLNat.pa.B(r))))]), List.append(&2, Nat, LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), [Nat.double(LLNat.pa.B(r))]),
    pa.vs_app(pa.lifts(pa.GV(r)), pa.line(d, LLNat.pa.B(r))),
    LLList.pa.app2(LLList.pa.vals(OPush.starts(pa.lifts(pa.GV(r)))), LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), OBits.Bits.val(OFit.pair_start(pa.line(d, LLNat.pa.B(r)))), Nat.double(LLNat.pa.B(r)),
      Equal.trans(List<&2, Nat>, LLList.pa.vals(OPush.starts(pa.lifts(pa.GV(r)))), LLList.pa.dbls(pa.SG(r)), LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), pa.vs_lifts(pa.GV(r)), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LLList.pa.dbls(z), pa.SG(r), LLList.pa.rev(LLList.pa.SE(r, 0n)), ih)),
      pa.vlast(d, LLNat.pa.B(r))))

def pa.sv_r(+r: List<&2, Bool>, +v1: Nat, e1: {v1 == Nat.double(LLNat.pa.B(r)) : Nat}) -> {List.reverse.go(&2, Nat, LLList.pa.SE(r, 1n), [v1]) == List.append(&2, Nat, LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), [Nat.double(LLNat.pa.B(r))]) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, List.reverse.go(&2, Nat, LLList.pa.SE(r, 1n), [v1]), List.append(&2, Nat, LLList.pa.rev(LLList.pa.SE(r, 1n)), [v1]), List.append(&2, Nat, LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), [Nat.double(LLNat.pa.B(r))]),
    LLList.pa.rev_app(LLList.pa.SE(r, 1n), [v1]),
    LLList.pa.app2(LLList.pa.rev(LLList.pa.SE(r, 1n)), LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), v1, Nat.double(LLNat.pa.B(r)),
      Equal.trans(List<&2, Nat>, LLList.pa.rev(LLList.pa.SE(r, 1n)), LLList.pa.rev(LLList.pa.dbls(LLList.pa.SE(r, 0n))), LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LLList.pa.rev(z), LLList.pa.SE(r, 1n), LLList.pa.dbls(LLList.pa.SE(r, 0n)), pa.vst(r, 0n)), LLList.pa.dbls_rev(LLList.pa.SE(r, 0n), Nil{})),
      e1))

# the view's starts are push's states, oldest first
def pa.sv(ds: List<&2, Bool>) -> {pa.SG(ds) == LLList.pa.rev(LLList.pa.SE(ds, 0n)) : List<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          Equal.trans(List<&2, Nat>, pa.SG(False{} <> r), List.append(&2, Nat, LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), [Nat.double(LLNat.pa.B(r))]), LLList.pa.rev(LLList.pa.SE(False{} <> r, 0n)), pa.sv_l(False{}, r, pa.sv(r)), Equal.sym(List<&2, Nat>, LLList.pa.rev(LLList.pa.SE(False{} <> r, 0n)), List.append(&2, Nat, LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), [Nat.double(LLNat.pa.B(r))]), pa.sv_r(r, OBits.Bits.val(LLList.pa.nb(LLNat.pa.sh(1n, LLNat.pa.B(r)))), pa.val_nb(LLNat.pa.sh(1n, LLNat.pa.B(r))))))
        case True{}:
          Equal.trans(List<&2, Nat>, pa.SG(True{} <> r), List.append(&2, Nat, LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), [Nat.double(LLNat.pa.B(r))]), LLList.pa.rev(LLList.pa.SE(True{} <> r, 0n)), pa.sv_l(True{}, r, pa.sv(r)), Equal.sym(List<&2, Nat>, LLList.pa.rev(LLList.pa.SE(True{} <> r, 0n)), List.append(&2, Nat, LLList.pa.dbls(LLList.pa.rev(LLList.pa.SE(r, 0n))), [Nat.double(LLNat.pa.B(r))]), pa.sv_r(r, OBits.Bits.val(LLList.pa.nb(LLNat.pa.sh(1n, LLNat.pa.B(r)))), pa.val_nb(LLNat.pa.sh(1n, LLNat.pa.B(r))))))

def pa.same_lines(+ds: List<&2, Bool>) -> {OPush.same_lines(pa.GV(ds), LLList.pa.GE(ds, 0n)) == True{} : Bool}:
  pa.same_vals(OPush.starts(pa.GV(ds)), List.reverse.go(&2, List<&2, Bool>, OPush.states(LLList.pa.GE(ds, 0n)), Nil{}), Equal.trans(List<&2, Nat>, pa.SG(ds), LLList.pa.rev(LLList.pa.SE(ds, 0n)), LLList.pa.vals(List.reverse.go(&2, List<&2, Bool>, OPush.states(LLList.pa.GE(ds, 0n)), Nil{})), pa.sv(ds), Equal.sym(List<&2, Nat>, LLList.pa.vals(List.reverse.go(&2, List<&2, Bool>, OPush.states(LLList.pa.GE(ds, 0n)), Nil{})), LLList.pa.rev(LLList.pa.SE(ds, 0n)), LLList.pa.vals_rev(OPush.states(LLList.pa.GE(ds, 0n)), Nil{}))))

def pa.len_lifts(xs: List<&2, ONode.Node>) -> {List.length(&2, ONode.Node, pa.lifts(xs)) == List.length(&2, ONode.Node, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      LNatMisc.pa.succ(List.length(&2, ONode.Node, pa.lifts(t)), List.length(&2, ONode.Node, t), pa.len_lifts(t))

def pa.len_GV(ds: List<&2, Bool>) -> {List.length(&2, ONode.Node, pa.GV(ds)) == List.length(&2, Bool, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +r:
      Equal.trans(Nat, List.length(&2, ONode.Node, pa.GV(d <> r)), 1n+List.length(&2, ONode.Node, pa.lifts(pa.GV(r))), 1n+List.length(&2, Bool, r),
        LLList.pa.len_app1(pa.lifts(pa.GV(r)), pa.line(d, LLNat.pa.B(r))),
        LNatMisc.pa.succ(List.length(&2, ONode.Node, pa.lifts(pa.GV(r))), List.length(&2, Bool, r), Equal.trans(Nat, List.length(&2, ONode.Node, pa.lifts(pa.GV(r))), List.length(&2, ONode.Node, pa.GV(r)), List.length(&2, Bool, r), pa.len_lifts(pa.GV(r)), pa.len_GV(r))))

# the higher lines of the view of r, then ys
def pa.size_hi(+r: List<&2, Bool>, +ys: List<&2, ONode.Node>) -> {LLNat.pa.vs(List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), ys)) == Nat.add(LLNat.pa.vs(ys), List.length(&2, Bool, r)) : Nat}:
  Equal.trans(Nat, LLNat.pa.vs(List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), ys)), Nat.add(LLNat.pa.vs(ys), List.length(&2, ONode.Node, pa.lifts(pa.GV(r)))), Nat.add(LLNat.pa.vs(ys), List.length(&2, Bool, r)),
    LLList.pa.size_app(pa.lifts(pa.GV(r)), ys),
    Equal.cong(Nat, Nat, z => Nat.add(LLNat.pa.vs(ys), z), List.length(&2, ONode.Node, pa.lifts(pa.GV(r))), List.length(&2, Bool, r), Equal.trans(Nat, List.length(&2, ONode.Node, pa.lifts(pa.GV(r))), List.length(&2, ONode.Node, pa.GV(r)), List.length(&2, Bool, r), pa.len_lifts(pa.GV(r)), pa.len_GV(r))))

# One level up
# ------------
# up(V, z): every line of V one level up, then a level-0 line z. With
# T + 2 doubled, the due order between lifted lines is the old one, so a
# fit of up(V, z) is the lifted fit of V.

def pa.up(v: List<&2, ONode.Node>, +z: ONode.Node) -> List<&2, ONode.Node>:
  List.append(&2, ONode.Node, pa.lifts(v), [z])

def pa.liftm(m: Maybe<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{pa.lift(x)}

def pa.shl_cons(l: Nat, +x: List<&2, Bool>) -> {OBits.Bits.shl(l, False{} <> x) == False{} <> OBits.Bits.shl(l, x) : List<&2, Bool>}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, z => False{} <> z, OBits.Bits.shl(p, False{} <> x), False{} <> OBits.Bits.shl(p, x), pa.shl_cons(p, x))

def pa.shl_ff(+l: Nat, +x: List<&2, Bool>) -> {False{} <> False{} <> OBits.Bits.shl(l, x) == OBits.Bits.shl(1n+l, False{} <> x) : List<&2, Bool>}:
  Equal.sym(List<&2, Bool>, OBits.Bits.shl(1n+l, False{} <> x), False{} <> False{} <> OBits.Bits.shl(l, x), Equal.cong(List<&2, Bool>, List<&2, Bool>, z => False{} <> z, OBits.Bits.shl(l, False{} <> x), False{} <> OBits.Bits.shl(l, x), pa.shl_cons(l, x)))

def pa.gt_ff(c: Cmp) -> {Cmp.is_gt(OBits.Cmp.then(OBits.Cmp.then(c, EQ{}), EQ{})) == Cmp.is_gt(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# both sides of the cross comparison times 4
def pa.cross_lift(+u: List<&2, Bool>, +la: Nat, +lb: Nat, +xa: List<&2, Bool>, +xb: List<&2, Bool>) -> {OFit.more_due.cross(False{} <> u, 1n+la, 1n+lb, False{} <> xa, False{} <> xb) == OFit.more_due.cross(u, la, lb, xa, xb) : Bool}:
  %pa.shl_ff(lb, u) : {OBits.Bits.gt(OBits.Bits.add(_, OBits.Bits.shl(1n+la, False{} <> xb)), OBits.Bits.add(OBits.Bits.shl(1n+la, False{} <> u), OBits.Bits.shl(1n+lb, False{} <> xa))) == OFit.more_due.cross(u, la, lb, xa, xb) : Bool}
  %pa.shl_ff(la, xb) : {OBits.Bits.gt(OBits.Bits.add(False{} <> False{} <> OBits.Bits.shl(lb, u), _), OBits.Bits.add(OBits.Bits.shl(1n+la, False{} <> u), OBits.Bits.shl(1n+lb, False{} <> xa))) == OFit.more_due.cross(u, la, lb, xa, xb) : Bool}
  %pa.shl_ff(la, u) : {OBits.Bits.gt(OBits.Bits.add(False{} <> False{} <> OBits.Bits.shl(lb, u), False{} <> False{} <> OBits.Bits.shl(la, xb)), OBits.Bits.add(_, OBits.Bits.shl(1n+lb, False{} <> xa))) == OFit.more_due.cross(u, la, lb, xa, xb) : Bool}
  %pa.shl_ff(lb, xa) : {OBits.Bits.gt(OBits.Bits.add(False{} <> False{} <> OBits.Bits.shl(lb, u), False{} <> False{} <> OBits.Bits.shl(la, xb)), OBits.Bits.add(False{} <> False{} <> OBits.Bits.shl(la, u), _)) == OFit.more_due.cross(u, la, lb, xa, xb) : Bool}
  pa.gt_ff(OBits.Bits.cmp(OBits.Bits.add(OBits.Bits.shl(lb, u), OBits.Bits.shl(la, xb)), OBits.Bits.add(OBits.Bits.shl(la, u), OBits.Bits.shl(lb, xa))))

# hu: T + 2 is twice T0 + 2
def pa.md_lift(+x: ONode.Node, +c: ONode.Node, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.more_due(OFit.Last{}, t, pa.lift(x), pa.lift(c)) == OFit.more_due(OFit.Last{}, t0, x, c) : Bool}:
  match x c:
    case ONode.Node{+lx, +ix} ONode.Node{+lc, +ic}:
      %hu : {OFit.more_due.cross(_, 1n+lx, 1n+lc, False{} <> OFit.pair_end(ONode.Node{lx, ix}), False{} <> OFit.pair_end(ONode.Node{lc, ic})) == OFit.more_due(OFit.Last{}, t0, ONode.Node{lx, ix}, ONode.Node{lc, ic}) : Bool}
      pa.cross_lift(OBits.Bits.inc(t0), lx, lc, OFit.pair_end(ONode.Node{lx, ix}), OFit.pair_end(ONode.Node{lc, ic}))

def pa.vs_lift(b: Bool, -x: ONode.Node, -c: ONode.Node) -> {OFit.best.vs(b, pa.lift(x), pa.lift(c)) == pa.lift(OFit.best.vs(b, x, c)) : ONode.Node}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pa.take_lift(cur: Maybe<&2, ONode.Node>, +x: ONode.Node, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.best.take(OFit.Last{}, t, pa.lift(x), pa.liftm(cur)) == pa.liftm(OFit.best.take(OFit.Last{}, t0, x, cur)) : Maybe<&2, ONode.Node>}:
  match cur:
    case None{}:
      {==}
    case Some{+c}:
      %Equal.sym(Bool, OFit.more_due(OFit.Last{}, t, pa.lift(x), pa.lift(c)), OFit.more_due(OFit.Last{}, t0, x, c), pa.md_lift(x, c, t, t0, hu)) : {Some{OFit.best.vs(_, pa.lift(x), pa.lift(c))} == Some{pa.lift(OFit.best.vs(OFit.more_due(OFit.Last{}, t0, x, c), x, c))} : Maybe<&2, ONode.Node>}
      Equal.cong(ONode.Node, Maybe<&2, ONode.Node>, z => Some{z}, OFit.best.vs(OFit.more_due(OFit.Last{}, t0, x, c), pa.lift(x), pa.lift(c)), pa.lift(OFit.best.vs(OFit.more_due(OFit.Last{}, t0, x, c), x, c)), pa.vs_lift(OFit.more_due(OFit.Last{}, t0, x, c), x, c))

def pa.pick_lift(ok: Bool, +cur: Maybe<&2, ONode.Node>, +x: ONode.Node, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.best.pick(ok, OFit.Last{}, t, pa.lift(x), pa.liftm(cur)) == pa.liftm(OFit.best.pick(ok, OFit.Last{}, t0, x, cur)) : Maybe<&2, ONode.Node>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      pa.take_lift(cur, x, t, t0, hu)

# the pair of x and the next line is mergeable in up(V, z) as in V; the
# last lifted line and z never are (z is level 0)
def pa.pair_lift(v: List<&2, ONode.Node>, +x: ONode.Node, +cur: Maybe<&2, ONode.Node>, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.best.pair(OFit.Last{}, t, OInfo.All{1n}, pa.lift(x), List.head(&2, ONode.Node, pa.up(v, ONode.Node{0n, iz})), pa.liftm(cur)) == pa.liftm(OFit.best.pair(OFit.Last{}, t0, OInfo.All{1n}, x, List.head(&2, ONode.Node, v), cur)) : Maybe<&2, ONode.Node>}:
  match v x:
    case Nil{} ONode.Node{lx, ix}:
      {==}
    case ONode.Node{+ly, +iy} <> w ONode.Node{+lx, +ix}:
      pa.pick_lift(OFit.mergeable(OInfo.All{1n}, ONode.Node{lx, ix}, ONode.Node{ly, iy}), cur, ONode.Node{lx, ix}, t, t0, hu)

def pa.best_lift(v: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.best.go(OFit.Last{}, t, OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz}), pa.liftm(cur)) == pa.liftm(OFit.best.go(OFit.Last{}, t0, OInfo.All{1n}, v, cur)) : Maybe<&2, ONode.Node>}:
  match v:
    case Nil{}:
      {==}
    case +x <> +w:
      %Equal.sym(Maybe<&2, ONode.Node>, OFit.best.pair(OFit.Last{}, t, OInfo.All{1n}, pa.lift(x), List.head(&2, ONode.Node, pa.up(w, ONode.Node{0n, iz})), pa.liftm(cur)), pa.liftm(OFit.best.pair(OFit.Last{}, t0, OInfo.All{1n}, x, List.head(&2, ONode.Node, w), cur)), pa.pair_lift(w, x, cur, iz, t, t0, hu)) : {OFit.best.go(OFit.Last{}, t, OInfo.All{1n}, pa.up(w, ONode.Node{0n, iz}), _) == pa.liftm(OFit.best.go(OFit.Last{}, t0, OInfo.All{1n}, x <> w, cur)) : Maybe<&2, ONode.Node>}
      pa.best_lift(w, OFit.best.pair(OFit.Last{}, t0, OInfo.All{1n}, x, List.head(&2, ONode.Node, w), cur), iz, t, t0, hu)

def pa.mpick_lift(h: Bool, +x: ONode.Node, +y: ONode.Node, +w: List<&2, ONode.Node>, +rec: List<&2, ONode.Node>, +z: ONode.Node)
  -> {OFit.merge.pick(h, pa.lift(x), pa.lift(y), pa.up(w, z), pa.up(rec, z)) == pa.up(OFit.merge.pick(h, x, y, w, rec), z) : List<&2, ONode.Node>}:
  match h x:
    case True{} ONode.Node{lx, ix}:
      {==}
    case False{} ONode.Node{lx, ix}:
      {==}

def pa.mpick_nil(h: Bool, +x: ONode.Node, +z: ONode.Node) -> {OFit.merge.pick(Bool.and(h, False{}), x, z, Nil{}, [z]) == [x, z] : List<&2, ONode.Node>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def pa.here_lift(w: List<&2, ONode.Node>, +x: ONode.Node, +a: ONode.Node, +iz: List<&2, Bool>)
  -> {OFit.merge.here(OInfo.All{1n}, pa.lift(a), pa.lift(x), pa.up(w, ONode.Node{0n, iz}), pa.up(OFit.merge(OInfo.All{1n}, w, a), ONode.Node{0n, iz})) == pa.up(OFit.merge.here(OInfo.All{1n}, a, x, w, OFit.merge(OInfo.All{1n}, w, a)), ONode.Node{0n, iz}) : List<&2, ONode.Node>}:
  match w x a:
    case Nil{} ONode.Node{+lx, +ix} ONode.Node{+la, +ia}:
      pa.mpick_nil(ONode.Node.eq(ONode.Node{lx, ix}, ONode.Node{la, ia}), ONode.Node{1n+lx, ix}, ONode.Node{0n, iz})
    case ONode.Node{+ly, +iy} <> +v ONode.Node{+lx, +ix} ONode.Node{+la, +ia}:
      pa.mpick_lift(Bool.and(ONode.Node.eq(ONode.Node{lx, ix}, ONode.Node{la, ia}), OFit.mergeable(OInfo.All{1n}, ONode.Node{lx, ix}, ONode.Node{ly, iy})), ONode.Node{lx, ix}, ONode.Node{ly, iy}, v, OFit.merge(OInfo.All{1n}, ONode.Node{ly, iy} <> v, ONode.Node{la, ia}), ONode.Node{0n, iz})

def pa.merge_lift(v: List<&2, ONode.Node>, +a: ONode.Node, +iz: List<&2, Bool>) -> {OFit.merge(OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz}), pa.lift(a)) == pa.up(OFit.merge(OInfo.All{1n}, v, a), ONode.Node{0n, iz}) : List<&2, ONode.Node>}:
  match v:
    case Nil{}:
      {==}
    case +x <> +w:
      %Equal.sym(List<&2, ONode.Node>, OFit.merge(OInfo.All{1n}, pa.up(w, ONode.Node{0n, iz}), pa.lift(a)), pa.up(OFit.merge(OInfo.All{1n}, w, a), ONode.Node{0n, iz}), pa.merge_lift(w, a, iz)) : {OFit.merge.here(OInfo.All{1n}, pa.lift(a), pa.lift(x), pa.up(w, ONode.Node{0n, iz}), _) == pa.up(OFit.merge(OInfo.All{1n}, x <> w, a), ONode.Node{0n, iz}) : List<&2, ONode.Node>}
      pa.here_lift(w, x, a, iz)

def pa.size_up(v: List<&2, ONode.Node>, +z: ONode.Node) -> {LLNat.pa.vs(pa.up(v, z)) == 1n+LLNat.pa.vs(v) : Nat}:
  match v:
    case Nil{}:
      {==}
    case h <> w:
      LNatMisc.pa.succ(LLNat.pa.vs(pa.up(w, z)), 1n+LLNat.pa.vs(w), pa.size_up(w, z))

def pa.cif_lift(over: Bool, +v: List<&2, ONode.Node>, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.choose.if(over, OFit.Last{}, t, OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz})) == pa.liftm(OFit.choose.if(over, OFit.Last{}, t0, OInfo.All{1n}, v)) : Maybe<&2, ONode.Node>}:
  match over:
    case False{}:
      {==}
    case True{}:
      pa.best_lift(v, None{}, iz, t, t0, hu)

def pa.choose_lift(+v: List<&2, ONode.Node>, +b: Nat, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz})) == pa.liftm(OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, v)) : Maybe<&2, ONode.Node>}:
  %Equal.sym(Nat, LLNat.pa.vs(pa.up(v, ONode.Node{0n, iz})), 1n+LLNat.pa.vs(v), pa.size_up(v, ONode.Node{0n, iz})) : {OFit.choose.if(Nat.is_gt(_, 1n+b), OFit.Last{}, t, OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz})) == pa.liftm(OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, v)) : Maybe<&2, ONode.Node>}
  pa.cif_lift(Nat.is_gt(LLNat.pa.vs(v), b), v, iz, t, t0, hu)

def pa.fit_lift(f: Nat, c: Maybe<&2, ONode.Node>, +v: List<&2, ONode.Node>, +b: Nat, +iz: List<&2, Bool>, +t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(f, pa.liftm(c), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz}))) == pa.up(Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(f, c, OFit.Last{}, t0, b, 0n, OInfo.All{1n}, v)), ONode.Node{0n, iz}) : List<&2, ONode.Node>}:
  match f c:
    case 0n _:
      {==}
    case 1n+g None{}:
      {==}
    case 1n++g Some{+a}:
      +m0 = OFit.merge(OInfo.All{1n}, v, a)
      r0 = OFit.fit.go(g, OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, m0), OFit.Last{}, t0, b, 0n, OInfo.All{1n}, m0)
      %LLPair.pa.snd_cons(ONode.Node.parent(pa.lift(a)), OFit.fit.go(g, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, OFit.merge(OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz}), pa.lift(a))), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, OFit.merge(OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz}), pa.lift(a)))) : {_ == pa.up(Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.cons(ONode.Node.parent(a), r0)), ONode.Node{0n, iz}) : List<&2, ONode.Node>}
      %LLPair.pa.snd_cons(ONode.Node.parent(a), r0) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(g, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, OFit.merge(OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz}), pa.lift(a))), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, OFit.merge(OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz}), pa.lift(a)))) == pa.up(_, ONode.Node{0n, iz}) : List<&2, ONode.Node>}
      %Equal.sym(List<&2, ONode.Node>, OFit.merge(OInfo.All{1n}, pa.up(v, ONode.Node{0n, iz}), pa.lift(a)), pa.up(m0, ONode.Node{0n, iz}), pa.merge_lift(v, a, iz)) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(g, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, _), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, _)) == pa.up(Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r0), ONode.Node{0n, iz}) : List<&2, ONode.Node>}
      %Equal.sym(Maybe<&2, ONode.Node>, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, pa.up(m0, ONode.Node{0n, iz})), pa.liftm(OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, m0)), pa.choose_lift(m0, b, iz, t, t0, hu)) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(g, _, OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, pa.up(m0, ONode.Node{0n, iz}))) == pa.up(Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r0), ONode.Node{0n, iz}) : List<&2, ONode.Node>}
      pa.fit_lift(g, OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, m0), m0, b, iz, t, t0, hu)

# Older lines end late enough
# ---------------------------
# Good(c, R): line c = node(l, i) of the view of R messages has
# (i + 3)·2^l >= R + 2, i.e. it ends at most 2^(l+1) - 2 messages before
# R: what follows it is at most two lines per lower level.

def pa.Good(c: ONode.Node, +R: Nat) -> Type:
  match c:
    case ONode.Node{l, i}:
      &k:Nat -> {LLNat.pa.sh(l, 3n+OBits.Bits.val(i)) == Nat.add(k, 2n+R) : Nat}

def pa.GoodAll(+R: Nat, xs: List<&2, ONode.Node>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case c <> t:
      (pa.Good(c, R) & pa.GoodAll(R, t))

def pa.good_lift(+d: Bool, c: ONode.Node, +R: Nat, g: pa.Good(c, R)) -> pa.Good(pa.lift(c), LLNat.pa.Bd(d, R)):
  match c:
    case ONode.Node{+l, +i}:
      (k0, e) = g
      +k = k0
      (LLNat.pa.bit_k(d, k), LLNat.pa.good_lift.eq(d, k, R, LLNat.pa.sh(l, 3n+OBits.Bits.val(i)), Equal.trans(Nat, Nat.double(LLNat.pa.sh(l, 3n+OBits.Bits.val(i))), Nat.double(Nat.add(k, 2n+R)), Nat.add(Nat.double(k), 4n+Nat.double(R)), Equal.cong(Nat, Nat, z => Nat.double(z), LLNat.pa.sh(l, 3n+OBits.Bits.val(i)), Nat.add(k, 2n+R), e), LLNat.pa.double_add(k, 2n+R))))

def pa.goods_lift(+d: Bool, xs: List<&2, ONode.Node>, +R: Nat, g: pa.GoodAll(R, xs)) -> pa.GoodAll(LLNat.pa.Bd(d, R), pa.lifts(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case c <> t:
      (gc, gt) = g
      (pa.good_lift(d, c, R, gc), pa.goods_lift(d, t, R, gt))

def pa.good_line(d: Bool, +R: Nat) -> pa.Good(pa.line(d, R), LLNat.pa.Bd(d, R)):
  match d:
    case False{}:
      (0n, Equal.cong(Nat, Nat, z => 3n+z, OBits.Bits.val(LLList.pa.nb(Nat.double(R))), Nat.double(R), pa.val_nb(Nat.double(R))))
    case True{}:
      (2n, Equal.cong(Nat, Nat, z => Nat.double(3n+z), OBits.Bits.val(LLList.pa.nb(R)), R, pa.val_nb(R)))

def pa.good_app(xs: List<&2, ONode.Node>, -y: ONode.Node, -R: Nat, gx: pa.GoodAll(R, xs), gy: pa.Good(y, R)) -> pa.GoodAll(R, List.append(&2, ONode.Node, xs, [y])):
  match xs:
    case Nil{}:
      (gy, Unit{})
    case c <> t:
      (gc, gt) = gx
      (gc, pa.good_app(t, y, R, gt, gy))

def pa.good_gv(ds: List<&2, Bool>) -> pa.GoodAll(LLNat.pa.B(ds), pa.GV(ds)):
  match ds:
    case Nil{}:
      Unit{}
    case d <> +r:
      match d:
        case False{}:
          pa.good_app(pa.lifts(pa.GV(r)), pa.line(False{}, LLNat.pa.B(r)), LLNat.pa.Bd(False{}, LLNat.pa.B(r)), pa.goods_lift(False{}, pa.GV(r), LLNat.pa.B(r), pa.good_gv(r)), pa.good_line(False{}, LLNat.pa.B(r)))
        case True{}:
          pa.good_app(pa.lifts(pa.GV(r)), pa.line(True{}, LLNat.pa.B(r)), LLNat.pa.Bd(True{}, LLNat.pa.B(r)), pa.goods_lift(True{}, pa.GV(r), LLNat.pa.B(r), pa.good_gv(r)), pa.good_line(True{}, LLNat.pa.B(r)))

# The newest pair is the most due
# -------------------------------
# With the lowest digit 0, T = 1 + 2R: line 0 is a0 = node(0, 2R), the new
# line b0 = node(0, 2R + 1), and the pair is due (T - last)/1 = 1. The
# older lines are the view of R lifted, each due less than 1 by Good:
# in the cross form, 2^l·(T + 2) + e_c > (T + 2) + 2^l·e_a.

def pa.a0(+R: Nat) -> ONode.Node:
  ONode.Node{0n, LLList.pa.nb(Nat.double(R))}

def pa.b0(+R: Nat) -> ONode.Node:
  ONode.Node{0n, True{} <> LLList.pa.nb(R)}

def pa.vii(+i: List<&2, Bool>) -> {OBits.Bits.val(OBits.Bits.inc(OBits.Bits.inc(i))) == 2n+OBits.Bits.val(i) : Nat}:
  Equal.trans(Nat, OBits.Bits.val(OBits.Bits.inc(OBits.Bits.inc(i))), 1n+OBits.Bits.val(OBits.Bits.inc(i)), 2n+OBits.Bits.val(i), pa.val_inc(OBits.Bits.inc(i)), LNatMisc.pa.succ(OBits.Bits.val(OBits.Bits.inc(i)), 1n+OBits.Bits.val(i), pa.val_inc(i)))

# T + 2 = 3 + 2R
def pa.vu(+R: Nat) -> {OBits.Bits.val(True{} <> OBits.Bits.inc(LLList.pa.nb(R))) == 3n+Nat.double(R) : Nat}:
  Equal.cong(Nat, Nat, z => 1n+Nat.double(z), OBits.Bits.val(OBits.Bits.inc(LLList.pa.nb(R))), 1n+R, Equal.trans(Nat, OBits.Bits.val(OBits.Bits.inc(LLList.pa.nb(R))), 1n+OBits.Bits.val(LLList.pa.nb(R)), 1n+R, pa.val_inc(LLList.pa.nb(R)), LNatMisc.pa.succ(OBits.Bits.val(LLList.pa.nb(R)), R, pa.val_nb(R))))

def pa.vX(+l: Nat, +R: Nat, +i: List<&2, Bool>)
  -> {OBits.Bits.val(OBits.Bits.add(False{} <> OBits.Bits.shl(l, True{} <> OBits.Bits.inc(LLList.pa.nb(R))), False{} <> OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(i))))) == Nat.add(Nat.double(LLNat.pa.sh(l, 3n+Nat.double(R))), Nat.double(LLNat.pa.sh(l, 2n+OBits.Bits.val(i)))) : Nat}:
  +U = {True{} <> OBits.Bits.inc(LLList.pa.nb(R)) : List<&2, Bool>}
  +II = OBits.Bits.inc(OBits.Bits.inc(i))
  Equal.trans(Nat, OBits.Bits.val(OBits.Bits.add(False{} <> OBits.Bits.shl(l, U), False{} <> OBits.Bits.shl(l, II))), Nat.add(Nat.double(OBits.Bits.val(OBits.Bits.shl(l, U))), Nat.double(OBits.Bits.val(OBits.Bits.shl(l, II)))), Nat.add(Nat.double(LLNat.pa.sh(l, 3n+Nat.double(R))), Nat.double(LLNat.pa.sh(l, 2n+OBits.Bits.val(i)))),
    pa.val_add(False{} <> OBits.Bits.shl(l, U), False{} <> OBits.Bits.shl(l, II), False{}),
    LLNat.pa.add2(Nat.double(OBits.Bits.val(OBits.Bits.shl(l, U))), Nat.double(LLNat.pa.sh(l, 3n+Nat.double(R))), Nat.double(OBits.Bits.val(OBits.Bits.shl(l, II))), Nat.double(LLNat.pa.sh(l, 2n+OBits.Bits.val(i))),
      Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(OBits.Bits.shl(l, U)), LLNat.pa.sh(l, 3n+Nat.double(R)), Equal.trans(Nat, OBits.Bits.val(OBits.Bits.shl(l, U)), LLNat.pa.sh(l, OBits.Bits.val(U)), LLNat.pa.sh(l, 3n+Nat.double(R)), pa.val_shl(l, U), Equal.cong(Nat, Nat, z => LLNat.pa.sh(l, z), OBits.Bits.val(U), 3n+Nat.double(R), pa.vu(R)))),
      Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(OBits.Bits.shl(l, II)), LLNat.pa.sh(l, 2n+OBits.Bits.val(i)), Equal.trans(Nat, OBits.Bits.val(OBits.Bits.shl(l, II)), LLNat.pa.sh(l, OBits.Bits.val(II)), LLNat.pa.sh(l, 2n+OBits.Bits.val(i)), pa.val_shl(l, II), Equal.cong(Nat, Nat, z => LLNat.pa.sh(l, z), OBits.Bits.val(II), 2n+OBits.Bits.val(i), pa.vii(i))))))

def pa.vY(+l: Nat, +R: Nat)
  -> {OBits.Bits.val(OBits.Bits.add(True{} <> OBits.Bits.inc(LLList.pa.nb(R)), False{} <> OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(LLList.pa.nb(Nat.double(R))))))) == Nat.add(3n+Nat.double(R), Nat.double(LLNat.pa.sh(l, 2n+Nat.double(R)))) : Nat}:
  +U = {True{} <> OBits.Bits.inc(LLList.pa.nb(R)) : List<&2, Bool>}
  +PA = OBits.Bits.inc(OBits.Bits.inc(LLList.pa.nb(Nat.double(R))))
  Equal.trans(Nat, OBits.Bits.val(OBits.Bits.add(U, False{} <> OBits.Bits.shl(l, PA))), Nat.add(OBits.Bits.val(U), Nat.double(OBits.Bits.val(OBits.Bits.shl(l, PA)))), Nat.add(3n+Nat.double(R), Nat.double(LLNat.pa.sh(l, 2n+Nat.double(R)))),
    pa.val_add(U, False{} <> OBits.Bits.shl(l, PA), False{}),
    LLNat.pa.add2(OBits.Bits.val(U), 3n+Nat.double(R), Nat.double(OBits.Bits.val(OBits.Bits.shl(l, PA))), Nat.double(LLNat.pa.sh(l, 2n+Nat.double(R))),
      pa.vu(R),
      Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(OBits.Bits.shl(l, PA)), LLNat.pa.sh(l, 2n+Nat.double(R)), Equal.trans(Nat, OBits.Bits.val(OBits.Bits.shl(l, PA)), LLNat.pa.sh(l, OBits.Bits.val(PA)), LLNat.pa.sh(l, 2n+Nat.double(R)), pa.val_shl(l, PA), Equal.cong(Nat, Nat, z => LLNat.pa.sh(l, z), OBits.Bits.val(PA), 2n+Nat.double(R), Equal.trans(Nat, OBits.Bits.val(PA), 2n+OBits.Bits.val(LLList.pa.nb(Nat.double(R))), 2n+Nat.double(R), pa.vii(LLList.pa.nb(Nat.double(R))), Equal.cong(Nat, Nat, z => 2n+z, OBits.Bits.val(LLList.pa.nb(Nat.double(R))), Nat.double(R), pa.val_nb(Nat.double(R)))))))))

# the pair (a0, b0) is more due than a lifted line of the view of R
def pa.old_one(c: ONode.Node, +R: Nat, g: pa.Good(c, R)) -> {OFit.more_due(OFit.Last{}, LLList.pa.tb0(R), pa.a0(R), pa.lift(c)) == True{} : Bool}:
  match c:
    case ONode.Node{+l, +i}:
      (k0, e) = g
      +k = k0
      +U = {True{} <> OBits.Bits.inc(LLList.pa.nb(R)) : List<&2, Bool>}
      +X = OBits.Bits.add(False{} <> OBits.Bits.shl(l, U), False{} <> OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(i))))
      +Y = OBits.Bits.add(U, False{} <> OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(LLList.pa.nb(Nat.double(R))))))
      -XX = Nat.add(Nat.double(LLNat.pa.sh(l, 3n+Nat.double(R))), Nat.double(LLNat.pa.sh(l, 2n+OBits.Bits.val(i))))
      +YY = Nat.add(3n+Nat.double(R), Nat.double(LLNat.pa.sh(l, 2n+Nat.double(R))))
      pa.gt_val(X, Y, LLNat.pa.old_one.gt(X, Y, XX, YY, k, pa.vX(l, R, i), pa.vY(l, R), LLNat.pa.ineq(l, R, OBits.Bits.val(i), k, e)))

def pa.eq_lift0(c: ONode.Node, -ia: List<&2, Bool>) -> {ONode.Node.eq(pa.lift(c), ONode.Node{0n, ia}) == False{} : Bool}:
  match c:
    case ONode.Node{l, i}:
      {==}

def pa.pre_lifts(xs: List<&2, ONode.Node>, +R: Nat, g: pa.GoodAll(R, xs)) -> LLList.pa.PreAll(LLList.pa.tb0(R), pa.a0(R), pa.lifts(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case +c <> t:
      (gc, gt) = g
      ((pa.old_one(c, R, gc), pa.eq_lift0(c, LLList.pa.nb(Nat.double(R)))), pa.pre_lifts(t, R, gt))

def pa.oldm_vs(b: Bool, -t: List<&2, Bool>, -a: ONode.Node, -x: ONode.Node, -c: ONode.Node, ox: {OFit.more_due(OFit.Last{}, t, a, x) == True{} : Bool}, oc: {OFit.more_due(OFit.Last{}, t, a, c) == True{} : Bool})
  -> LLList.pa.OldM(t, a, Some{OFit.best.vs(b, x, c)}):
  match b:
    case True{}:
      ox
    case False{}:
      oc

def pa.oldm_take(cur: Maybe<&2, ONode.Node>, +t: List<&2, Bool>, -a: ONode.Node, +x: ONode.Node, ox: {OFit.more_due(OFit.Last{}, t, a, x) == True{} : Bool}, oc: LLList.pa.OldM(t, a, cur))
  -> LLList.pa.OldM(t, a, OFit.best.take(OFit.Last{}, t, x, cur)):
  match cur:
    case None{}:
      ox
    case Some{+c}:
      pa.oldm_vs(OFit.more_due(OFit.Last{}, t, x, c), t, a, x, c, ox, oc)

def pa.oldm_pick(ok: Bool, +cur: Maybe<&2, ONode.Node>, +t: List<&2, Bool>, -a: ONode.Node, +x: ONode.Node, ox: {OFit.more_due(OFit.Last{}, t, a, x) == True{} : Bool}, oc: LLList.pa.OldM(t, a, cur))
  -> LLList.pa.OldM(t, a, OFit.best.pick(ok, OFit.Last{}, t, x, cur)):
  match ok:
    case False{}:
      oc
    case True{}:
      pa.oldm_take(cur, t, a, x, ox, oc)

def pa.oldm_pair(nxt: Maybe<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +t: List<&2, Bool>, -a: ONode.Node, +x: ONode.Node, ox: {OFit.more_due(OFit.Last{}, t, a, x) == True{} : Bool}, oc: LLList.pa.OldM(t, a, cur))
  -> LLList.pa.OldM(t, a, OFit.best.pair(OFit.Last{}, t, OInfo.All{1n}, x, nxt, cur)):
  match nxt:
    case None{}:
      oc
    case Some{+y}:
      pa.oldm_pick(OFit.mergeable(OInfo.All{1n}, x, y), cur, t, a, x, ox, oc)

def pa.take_base(cur: Maybe<&2, ONode.Node>, +t: List<&2, Bool>, +a: ONode.Node, +b: ONode.Node, oc: LLList.pa.OldM(t, a, cur))
  -> {OFit.best.go(OFit.Last{}, t, OInfo.All{1n}, [b], OFit.best.take(OFit.Last{}, t, a, cur)) == Some{a} : Maybe<&2, ONode.Node>}:
  match cur:
    case None{}:
      {==}
    case Some{+c}:
      %Equal.sym(Bool, OFit.more_due(OFit.Last{}, t, a, c), True{}, oc) : {OFit.best.go(OFit.Last{}, t, OInfo.All{1n}, [b], Some{OFit.best.vs(_, a, c)}) == Some{a} : Maybe<&2, ONode.Node>}
      {==}

# best picks a when (a, b) may merge, comes last, and beats every line
# before it
def pa.best_base(xs: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +t: List<&2, Bool>, +a: ONode.Node, +b: ONode.Node, +mab: {OFit.mergeable(OInfo.All{1n}, a, b) == True{} : Bool}, pre: LLList.pa.PreAll(t, a, xs), oc: LLList.pa.OldM(t, a, cur))
  -> {OFit.best.go(OFit.Last{}, t, OInfo.All{1n}, List.append(&2, ONode.Node, xs, [a, b]), cur) == Some{a} : Maybe<&2, ONode.Node>}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, OFit.mergeable(OInfo.All{1n}, a, b), True{}, mab) : {OFit.best.go(OFit.Last{}, t, OInfo.All{1n}, [b], OFit.best.pick(_, OFit.Last{}, t, a, cur)) == Some{a} : Maybe<&2, ONode.Node>}
      pa.take_base(cur, t, a, b, oc)
    case +x <> +r:
      (px, pr) = pre
      (ox, ex) = px
      pa.best_base(r, OFit.best.pair(OFit.Last{}, t, OInfo.All{1n}, x, List.head(&2, ONode.Node, List.append(&2, ONode.Node, r, [a, b])), cur), t, a, b, mab, pr, pa.oldm_pair(List.head(&2, ONode.Node, List.append(&2, ONode.Node, r, [a, b])), cur, t, a, x, ox, oc))

def pa.node_eq_self(n: ONode.Node) -> {ONode.Node.eq(n, n) == True{} : Bool}:
  match n:
    case ONode.Node{+l, +i}:
      %Equal.sym(Bool, OBits.Bits.same(i, i), True{}, pa.same_val(i, i, {==})) : {Bool.and(Nat.is_eq(l, l), _) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(l, l), EQ{}, LLNat.pa.cmp_self(l)) : {Bool.and(Cmp.is_eq(_), True{}) == True{} : Bool}
      {==}

def pa.mhere_base(xs: List<&2, ONode.Node>, +x: ONode.Node, +a: ONode.Node, +b: ONode.Node, ex: {ONode.Node.eq(x, a) == False{} : Bool})
  -> {OFit.merge.here(OInfo.All{1n}, a, x, List.append(&2, ONode.Node, xs, [a, b]), List.append(&2, ONode.Node, xs, [ONode.Node.parent(a)])) == x <> List.append(&2, ONode.Node, xs, [ONode.Node.parent(a)]) : List<&2, ONode.Node>}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, ONode.Node.eq(x, a), False{}, ex) : {OFit.merge.pick(Bool.and(_, OFit.mergeable(OInfo.All{1n}, x, a)), x, a, [b], [ONode.Node.parent(a)]) == [x, ONode.Node.parent(a)] : List<&2, ONode.Node>}
      {==}
    case +y <> +r:
      %Equal.sym(Bool, ONode.Node.eq(x, a), False{}, ex) : {OFit.merge.pick(Bool.and(_, OFit.mergeable(OInfo.All{1n}, x, y)), x, y, List.append(&2, ONode.Node, r, [a, b]), y <> List.append(&2, ONode.Node, r, [ONode.Node.parent(a)])) == x <> y <> List.append(&2, ONode.Node, r, [ONode.Node.parent(a)]) : List<&2, ONode.Node>}
      {==}

# the merge of a replaces (a, b) by their parent
def pa.merge_base(xs: List<&2, ONode.Node>, +a: ONode.Node, +b: ONode.Node, +mab: {OFit.mergeable(OInfo.All{1n}, a, b) == True{} : Bool}, -t: List<&2, Bool>, pre: LLList.pa.PreAll(t, a, xs))
  -> {OFit.merge(OInfo.All{1n}, List.append(&2, ONode.Node, xs, [a, b]), a) == List.append(&2, ONode.Node, xs, [ONode.Node.parent(a)]) : List<&2, ONode.Node>}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, ONode.Node.eq(a, a), True{}, pa.node_eq_self(a)) : {OFit.merge.pick(Bool.and(_, OFit.mergeable(OInfo.All{1n}, a, b)), a, b, Nil{}, OFit.merge(OInfo.All{1n}, [b], a)) == [ONode.Node.parent(a)] : List<&2, ONode.Node>}
      %Equal.sym(Bool, OFit.mergeable(OInfo.All{1n}, a, b), True{}, mab) : {OFit.merge.pick(Bool.and(True{}, _), a, b, Nil{}, OFit.merge(OInfo.All{1n}, [b], a)) == [ONode.Node.parent(a)] : List<&2, ONode.Node>}
      {==}
    case +x <> +r:
      (px, pr) = pre
      (ox, ex) = px
      %Equal.sym(List<&2, ONode.Node>, OFit.merge(OInfo.All{1n}, List.append(&2, ONode.Node, r, [a, b]), a), List.append(&2, ONode.Node, r, [ONode.Node.parent(a)]), pa.merge_base(r, a, b, mab, t, pr)) : {OFit.merge.here(OInfo.All{1n}, a, x, List.append(&2, ONode.Node, r, [a, b]), _) == x <> List.append(&2, ONode.Node, r, [ONode.Node.parent(a)]) : List<&2, ONode.Node>}
      pa.mhere_base(r, x, a, b, ex)

def pa.mab(+R: Nat) -> {OFit.mergeable(OInfo.All{1n}, pa.a0(R), pa.b0(R)) == True{} : Bool}:
  %Equal.sym(Bool, OBits.Bits.low(LLList.pa.nb(Nat.double(R))), False{}, pa.low_even(R)) : {Bool.and(Bool.and(Bool.not(_), OBits.Bits.eq(OBits.Bits.up(LLList.pa.nb(Nat.double(R))), LLList.pa.nb(R))), True{}) == True{} : Bool}
  %Equal.sym(List<&2, Bool>, OBits.Bits.up(LLList.pa.nb(Nat.double(R))), LLList.pa.nb(R), pa.up_even(R)) : {Bool.and(OBits.Bits.eq(_, LLList.pa.nb(R)), True{}) == True{} : Bool}
  %Equal.sym(Bool, OBits.Bits.eq(LLList.pa.nb(R), LLList.pa.nb(R)), True{}, pa.bits_eq_self(LLList.pa.nb(R))) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def pa.lifts_app1(xs: List<&2, ONode.Node>, +y: ONode.Node) -> {pa.lifts(List.append(&2, ONode.Node, xs, [y])) == List.append(&2, ONode.Node, pa.lifts(xs), [pa.lift(y)]) : List<&2, ONode.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, z => pa.lift(h) <> z, pa.lifts(List.append(&2, ONode.Node, t, [y])), List.append(&2, ONode.Node, pa.lifts(t), [pa.lift(y)]), pa.lifts_app1(t, y))

def pa.V(+ds: List<&2, Bool>) -> List<&2, ONode.Node>:
  List.append(&2, ONode.Node, pa.GV(ds), [ONode.Node.leaf(LLList.pa.nb(LLNat.pa.B(ds)))])

# the fit of one step (with any fuel above 0) is the view of T + 1
def pa.FT(+ds: List<&2, Bool>, +f: Nat) -> Type:
  {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, OFit.choose(OFit.Last{}, LLList.pa.T2(ds), LLList.pa.bud(ds), 0n, OInfo.All{1n}, pa.V(ds)), OFit.Last{}, LLList.pa.T2(ds), LLList.pa.bud(ds), 0n, OInfo.All{1n}, pa.V(ds))) == pa.GV(LLList.pa.inc(ds)) : List<&2, ONode.Node>}

def pa.hc_base(+r: List<&2, Bool>)
  -> {OFit.choose(OFit.Last{}, LLList.pa.tb0(LLNat.pa.B(r)), 1n+List.length(&2, Bool, r), 0n, OInfo.All{1n}, List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), [pa.a0(LLNat.pa.B(r)), pa.b0(LLNat.pa.B(r))])) == Some{pa.a0(LLNat.pa.B(r))} : Maybe<&2, ONode.Node>}:
  +R = LLNat.pa.B(r)
  +y = List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), [pa.a0(R), pa.b0(R)])
  %Equal.sym(Nat, LLNat.pa.vs(y), 2n+List.length(&2, Bool, r), pa.size_hi(r, [pa.a0(R), pa.b0(R)])) : {OFit.choose.if(Nat.is_gt(_, 1n+List.length(&2, Bool, r)), OFit.Last{}, LLList.pa.tb0(R), OInfo.All{1n}, y) == Some{pa.a0(R)} : Maybe<&2, ONode.Node>}
  %Equal.sym(Bool, Nat.is_gt(1n+List.length(&2, Bool, r), List.length(&2, Bool, r)), True{}, LLNat.pa.gt_succ(List.length(&2, Bool, r))) : {OFit.choose.if(_, OFit.Last{}, LLList.pa.tb0(R), OInfo.All{1n}, y) == Some{pa.a0(R)} : Maybe<&2, ONode.Node>}
  pa.best_base(pa.lifts(pa.GV(r)), None{}, LLList.pa.tb0(R), pa.a0(R), pa.b0(R), pa.mab(R), pa.pre_lifts(pa.GV(r), R, pa.good_gv(r)), Unit{})

def pa.hm_base(+r: List<&2, Bool>)
  -> {OFit.merge(OInfo.All{1n}, List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), [pa.a0(LLNat.pa.B(r)), pa.b0(LLNat.pa.B(r))]), pa.a0(LLNat.pa.B(r))) == pa.GV(True{} <> r) : List<&2, ONode.Node>}:
  +R = LLNat.pa.B(r)
  Equal.trans(List<&2, ONode.Node>, OFit.merge(OInfo.All{1n}, List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), [pa.a0(R), pa.b0(R)]), pa.a0(R)), List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), [ONode.Node.parent(pa.a0(R))]), pa.GV(True{} <> r),
    pa.merge_base(pa.lifts(pa.GV(r)), pa.a0(R), pa.b0(R), pa.mab(R), LLList.pa.tb0(R), pa.pre_lifts(pa.GV(r), R, pa.good_gv(r))),
    Equal.cong(List<&2, Bool>, List<&2, ONode.Node>, z => List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), [ONode.Node{1n, z}]), OBits.Bits.up(LLList.pa.nb(Nat.double(R))), LLList.pa.nb(R), pa.up_even(R)))

def pa.hn_base(+r: List<&2, Bool>)
  -> {OFit.choose(OFit.Last{}, LLList.pa.tb0(LLNat.pa.B(r)), 1n+List.length(&2, Bool, r), 0n, OInfo.All{1n}, pa.GV(True{} <> r)) == None{} : Maybe<&2, ONode.Node>}:
  +R = LLNat.pa.B(r)
  %Equal.sym(Nat, LLNat.pa.vs(pa.GV(True{} <> r)), 1n+List.length(&2, Bool, r), pa.size_hi(r, [ONode.Node{1n, LLList.pa.nb(R)}])) : {OFit.choose.if(Nat.is_gt(_, 1n+List.length(&2, Bool, r)), OFit.Last{}, LLList.pa.tb0(R), OInfo.All{1n}, pa.GV(True{} <> r)) == None{} : Maybe<&2, ONode.Node>}
  %Equal.sym(Bool, Nat.is_gt(1n+List.length(&2, Bool, r), 1n+List.length(&2, Bool, r)), False{}, LLNat.pa.gt_self(1n+List.length(&2, Bool, r))) : {OFit.choose.if(_, OFit.Last{}, LLList.pa.tb0(R), OInfo.All{1n}, pa.GV(True{} <> r)) == None{} : Maybe<&2, ONode.Node>}
  {==}

# lowest digit 0: the new line merges with line 0
def pa.F_base(+r: List<&2, Bool>, +f: Nat) -> pa.FT(False{} <> r, f):
  +R = LLNat.pa.B(r)
  +X = pa.lifts(pa.GV(r))
  +n = {1n+List.length(&2, Bool, r) : Nat}
  %Equal.sym(List<&2, Bool>, LLList.pa.nb(1n+Nat.double(R)), True{} <> LLList.pa.nb(R), LLList.pa.nb_odd(R)) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, OFit.choose(OFit.Last{}, OBits.Bits.inc(_), n, 0n, OInfo.All{1n}, List.append(&2, ONode.Node, List.append(&2, ONode.Node, X, [pa.a0(R)]), [ONode.Node{0n, _}])), OFit.Last{}, OBits.Bits.inc(_), n, 0n, OInfo.All{1n}, List.append(&2, ONode.Node, List.append(&2, ONode.Node, X, [pa.a0(R)]), [ONode.Node{0n, _}]))) == pa.GV(True{} <> r) : List<&2, ONode.Node>}
  %Equal.sym(List<&2, ONode.Node>, List.append(&2, ONode.Node, List.append(&2, ONode.Node, X, [pa.a0(R)]), [pa.b0(R)]), List.append(&2, ONode.Node, X, [pa.a0(R), pa.b0(R)]), LLList.pa.app_ab(X, pa.a0(R), pa.b0(R))) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, OFit.choose(OFit.Last{}, LLList.pa.tb0(R), n, 0n, OInfo.All{1n}, _), OFit.Last{}, LLList.pa.tb0(R), n, 0n, OInfo.All{1n}, _)) == pa.GV(True{} <> r) : List<&2, ONode.Node>}
  LLPair.pa.base_fit(f, List.append(&2, ONode.Node, X, [pa.a0(R), pa.b0(R)]), pa.a0(R), pa.GV(True{} <> r), LLList.pa.tb0(R), n, pa.hc_base(r), pa.hm_base(r), pa.hn_base(r))

# lowest digit 1: the step is the lifted step of the higher digits
def pa.F_lift(+r: List<&2, Bool>, +f: Nat, ih: pa.FT(r, f)) -> pa.FT(True{} <> r, f):
  +R = LLNat.pa.B(r)
  +iz = LLList.pa.nb(2n+Nat.double(R))
  +t = LLList.pa.T2(True{} <> r)
  +t0 = LLList.pa.T2(r)
  +b = LLList.pa.bud(r)
  +c0 = OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, pa.V(r))
  +hu = Equal.sym(List<&2, Bool>, OBits.Bits.inc(OBits.Bits.inc(LLList.pa.nb(2n+Nat.double(R)))), OBits.Bits.inc(OBits.Bits.inc(False{} <> LLList.pa.nb(1n+R))), Equal.cong(List<&2, Bool>, List<&2, Bool>, z => OBits.Bits.inc(OBits.Bits.inc(z)), LLList.pa.nb(2n+Nat.double(R)), False{} <> LLList.pa.nb(1n+R), LLList.pa.nb_even(R)))
  %Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, w => List.append(&2, ONode.Node, w, [ONode.Node{0n, iz}]), pa.lifts(List.append(&2, ONode.Node, pa.GV(r), [ONode.Node{0n, LLList.pa.nb(R)}])), List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), [pa.lift(ONode.Node{0n, LLList.pa.nb(R)})]), pa.lifts_app1(pa.GV(r), ONode.Node{0n, LLList.pa.nb(R)})) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, _), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, _)) == pa.GV(False{} <> LLList.pa.inc(r)) : List<&2, ONode.Node>}
  %Equal.sym(Maybe<&2, ONode.Node>, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, pa.up(pa.V(r), ONode.Node{0n, iz})), pa.liftm(c0), pa.choose_lift(pa.V(r), b, iz, t, t0, hu)) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, _, OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, pa.up(pa.V(r), ONode.Node{0n, iz}))) == pa.GV(False{} <> LLList.pa.inc(r)) : List<&2, ONode.Node>}
  -S0 = Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, c0, OFit.Last{}, t0, b, 0n, OInfo.All{1n}, pa.V(r)))
  Equal.trans(List<&2, ONode.Node>, Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, pa.liftm(c0), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, pa.up(pa.V(r), ONode.Node{0n, iz}))), pa.up(S0, ONode.Node{0n, iz}), pa.GV(False{} <> LLList.pa.inc(r)),
    pa.fit_lift(1n+f, c0, pa.V(r), b, iz, t, t0, hu),
    Equal.trans(List<&2, ONode.Node>, pa.up(S0, ONode.Node{0n, iz}), pa.up(pa.GV(LLList.pa.inc(r)), ONode.Node{0n, iz}), pa.GV(False{} <> LLList.pa.inc(r)),
      Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, w => pa.up(w, ONode.Node{0n, iz}), S0, pa.GV(LLList.pa.inc(r)), ih),
      Equal.cong(Nat, List<&2, ONode.Node>, w => List.append(&2, ONode.Node, pa.lifts(pa.GV(LLList.pa.inc(r))), [ONode.Node{0n, LLList.pa.nb(Nat.double(w))}]), 1n+R, LLNat.pa.B(LLList.pa.inc(r)), Equal.sym(Nat, LLNat.pa.B(LLList.pa.inc(r)), 1n+R, LLList.pa.B_inc(r)))))

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
def pa.step(+ds: List<&2, Bool>) -> {OFit.fit.view(OFit.Last{}, LLList.pa.T2(ds), List.length(&2, OPush.Entry, LLList.pa.GE(LLList.pa.inc(ds), 0n)), 0n, OInfo.All{1n}, pa.V(ds)) == pa.GV(LLList.pa.inc(ds)) : List<&2, ONode.Node>}:
  %Equal.sym(Nat, List.length(&2, OPush.Entry, LLList.pa.GE(LLList.pa.inc(ds), 0n)), LLList.pa.bud(ds), LLList.pa.len_GE(LLList.pa.inc(ds), 0n)) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(List.length(&2, ONode.Node, pa.V(ds)), OFit.choose(OFit.Last{}, LLList.pa.T2(ds), _, 0n, OInfo.All{1n}, pa.V(ds)), OFit.Last{}, LLList.pa.T2(ds), _, 0n, OInfo.All{1n}, pa.V(ds))) == pa.GV(LLList.pa.inc(ds)) : List<&2, ONode.Node>}
  %Equal.sym(Nat, List.length(&2, ONode.Node, pa.V(ds)), 1n+List.length(&2, ONode.Node, pa.GV(ds)), LLList.pa.len_app1(pa.GV(ds), ONode.Node.leaf(LLList.pa.nb(LLNat.pa.B(ds))))) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(_, OFit.choose(OFit.Last{}, LLList.pa.T2(ds), LLList.pa.bud(ds), 0n, OInfo.All{1n}, pa.V(ds)), OFit.Last{}, LLList.pa.T2(ds), LLList.pa.bud(ds), 0n, OInfo.All{1n}, pa.V(ds))) == pa.GV(LLList.pa.inc(ds)) : List<&2, ONode.Node>}
  pa.F(ds, List.length(&2, ONode.Node, pa.GV(ds)))

# The law
# -------

def pa.agree(n: Nat, +ds: List<&2, Bool>) -> {OPush.agree.go(n, OFit.Last{}, LLList.pa.nb(LLNat.pa.B(ds)), LLList.pa.GE(ds, 0n), pa.GV(ds)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +es2 = LLList.pa.GE(LLList.pa.inc(ds), 0n)
      +v2 = pa.GV(LLList.pa.inc(ds))
      %Equal.sym(List<&2, OPush.Entry>, OPush.push(LLList.pa.GE(ds, 0n), LLList.pa.nb(LLNat.pa.B(ds))), es2, pa.push_ge(ds, 0n)) : {Bool.and(OPush.same_lines(OFit.fit.view(OFit.Last{}, LLList.pa.T2(ds), List.length(&2, OPush.Entry, _), 0n, OInfo.All{1n}, pa.V(ds)), _), OPush.agree.go(p, OFit.Last{}, LLList.pa.T2(ds), _, OFit.fit.view(OFit.Last{}, LLList.pa.T2(ds), List.length(&2, OPush.Entry, _), 0n, OInfo.All{1n}, pa.V(ds)))) == True{} : Bool}
      %Equal.sym(List<&2, ONode.Node>, OFit.fit.view(OFit.Last{}, LLList.pa.T2(ds), List.length(&2, OPush.Entry, es2), 0n, OInfo.All{1n}, pa.V(ds)), v2, pa.step(ds)) : {Bool.and(OPush.same_lines(_, es2), OPush.agree.go(p, OFit.Last{}, LLList.pa.T2(ds), es2, _)) == True{} : Bool}
      %LLList.pa.B_inc(ds) : {Bool.and(OPush.same_lines(v2, es2), OPush.agree.go(p, OFit.Last{}, LLList.pa.nb(_), es2, v2)) == True{} : Bool}
      %Equal.sym(Bool, OPush.same_lines(v2, es2), True{}, pa.same_lines(LLList.pa.inc(ds))) : {Bool.and(_, OPush.agree.go(p, OFit.Last{}, LLList.pa.nb(LLNat.pa.B(LLList.pa.inc(ds))), es2, v2)) == True{} : Bool}
      pa.agree(p, LLList.pa.inc(ds))

def push_agrees_always(n: Nat) -> {OPush.agree(OFit.Last{}, n) == True{} : Bool}:
  pa.agree(n, Nil{})
