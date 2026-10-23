# eukhe: lemmas of the proof of LAW push_agrees_always: optchat

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/fit.bend as OFit
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/push.bend as OPush
import ../../base/logic/nat.bend as LLogicNat
import ../../base/nat.bend as LNat
import ../base.bend as LA
import ./list.bend as LLList
import ./logic.bend as LLLogic
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

def pa.val_shl(l: Nat, +x: List<&2, Bool>) -> {OBits.Bits.val(OBits.Bits.shl(l, x)) == LLLogic.pa.sh(l, OBits.Bits.val(x)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(OBits.Bits.shl(p, x)), LLLogic.pa.sh(p, OBits.Bits.val(x)), pa.val_shl(p, x))

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
          Equal.sym(Nat, Nat.add(OBits.Bits.val(x <> xt), 0n), OBits.Bits.val(x <> xt), LNat.pa.add_zero(OBits.Bits.val(x <> xt)))
        case True{}:
          Equal.trans(Nat, OBits.Bits.val(OBits.Bits.inc(x <> xt)), 1n+OBits.Bits.val(x <> xt), 1n+Nat.add(OBits.Bits.val(x <> xt), 0n), pa.val_inc(x <> xt), LLogicNat.pa.succ(OBits.Bits.val(x <> xt), Nat.add(OBits.Bits.val(x <> xt), 0n), Equal.sym(Nat, Nat.add(OBits.Bits.val(x <> xt), 0n), OBits.Bits.val(x <> xt), LNat.pa.add_zero(OBits.Bits.val(x <> xt)))))
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

def pa.val_nb(+n: Nat) -> {OBits.Bits.val(LLLogic.pa.nb(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, OBits.Bits.val(OBits.Bits.inc(LLLogic.pa.nb(p))), 1n+OBits.Bits.val(LLLogic.pa.nb(p)), 1n+p, pa.val_inc(LLLogic.pa.nb(p)), LLogicNat.pa.succ(OBits.Bits.val(LLLogic.pa.nb(p)), p, pa.val_nb(p)))

def pa.low_even(+r: Nat) -> {OBits.Bits.low(LLLogic.pa.nb(Nat.double(r))) == False{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, Bool>, LLLogic.pa.nb(2n+Nat.double(p)), False{} <> LLLogic.pa.nb(1n+p), LLNat.pa.nb_even(p)) : {OBits.Bits.low(_) == False{} : Bool}
      {==}

def pa.up_even(+r: Nat) -> {OBits.Bits.up(LLLogic.pa.nb(Nat.double(r))) == LLLogic.pa.nb(r) : List<&2, Bool>}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, Bool>, LLLogic.pa.nb(2n+Nat.double(p)), False{} <> LLLogic.pa.nb(1n+p), LLNat.pa.nb_even(p)) : {OBits.Bits.up(_) == LLLogic.pa.nb(1n+p) : List<&2, Bool>}
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

# Push is the counter
# -------------------

def pa.push_ge(ds: List<&2, Bool>, +j: Nat) -> {OPush.push(LLLogic.pa.GE(ds, j), LLLogic.pa.nb(LLLogic.pa.sh(j, LLLogic.pa.B(ds)))) == LLLogic.pa.GE(LLLogic.pa.inc(ds), j) : List<&2, OPush.Entry>}:
  match ds:
    case Nil{}:
      %Equal.sym(Nat, LLLogic.pa.sh(j, 0n), 0n, LLLogic.pa.sh_zero(j)) : {[OPush.Entry{0n, 0n, LLLogic.pa.nb(_)}] == [OPush.Entry{0n, 0n, LLLogic.pa.nb(Nat.double(_))}] : List<&2, OPush.Entry>}
      {==}
    case d <> +r:
      match d:
        case False{}:
          {==}
        case True{}:
          %pa.push_ge(r, 1n+j) : {OPush.Entry{0n, 0n, LLLogic.pa.nb(LLLogic.pa.sh(j, 2n+Nat.double(LLLogic.pa.B(r))))} <> OPush.push(LLLogic.pa.GE(r, 1n+j), LLLogic.pa.nb(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r)))) == OPush.Entry{0n, 0n, LLLogic.pa.nb(LLLogic.pa.sh(1n+j, LLLogic.pa.B(LLLogic.pa.inc(r))))} <> _ : List<&2, OPush.Entry>}
          %LLLogic.pa.B_inc(r) : {OPush.Entry{0n, 0n, LLLogic.pa.nb(LLLogic.pa.sh(j, Nat.double(_)))} <> OPush.push(LLLogic.pa.GE(r, 1n+j), LLLogic.pa.nb(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r)))) == OPush.Entry{0n, 0n, LLLogic.pa.nb(LLLogic.pa.sh(1n+j, LLLogic.pa.B(LLLogic.pa.inc(r))))} <> OPush.push(LLLogic.pa.GE(r, 1n+j), LLLogic.pa.nb(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r)))) : List<&2, OPush.Entry>}
          %LLNat.pa.sh_double(j, LLLogic.pa.B(LLLogic.pa.inc(r))) : {OPush.Entry{0n, 0n, LLLogic.pa.nb(LLLogic.pa.sh(j, Nat.double(LLLogic.pa.B(LLLogic.pa.inc(r)))))} <> OPush.push(LLLogic.pa.GE(r, 1n+j), LLLogic.pa.nb(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r)))) == OPush.Entry{0n, 0n, LLLogic.pa.nb(_)} <> OPush.push(LLLogic.pa.GE(r, 1n+j), LLLogic.pa.nb(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r)))) : List<&2, OPush.Entry>}
          {==}

def pa.same_vals(xs: List<&2, List<&2, Bool>>, ys: List<&2, List<&2, Bool>>, +e: {LLLogic.pa.vals(xs) == LLLogic.pa.vals(ys) : List<&2, Nat>}) -> {OPush.Bitss.same(xs, ys) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      LLLogic.pa.nil_cons({False{} == True{} : Bool}, OBits.Bits.val(y), LLLogic.pa.vals(yt), e)
    case +x <> +xt Nil{}:
      LLLogic.pa.nil_cons({False{} == True{} : Bool}, OBits.Bits.val(x), LLLogic.pa.vals(xt), Equal.sym(List<&2, Nat>, OBits.Bits.val(x) <> LLLogic.pa.vals(xt), Nil{}, e))
    case +x <> +xt +y <> +yt:
      %Equal.sym(Bool, OBits.Bits.same(x, y), True{}, pa.same_val(x, y, Equal.cong(List<&2, Nat>, Nat, z => LLLogic.pa.hd(z), OBits.Bits.val(x) <> LLLogic.pa.vals(xt), OBits.Bits.val(y) <> LLLogic.pa.vals(yt), e))) : {Bool.and(_, OPush.Bitss.same(xt, yt)) == True{} : Bool}
      pa.same_vals(xt, yt, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LLLogic.pa.tl(z), OBits.Bits.val(x) <> LLLogic.pa.vals(xt), OBits.Bits.val(y) <> LLLogic.pa.vals(yt), e))

# val(nb(2x)) = 2·val(nb(x))
def pa.val_nb2(+x: Nat) -> {OBits.Bits.val(LLLogic.pa.nb(Nat.double(x))) == Nat.double(OBits.Bits.val(LLLogic.pa.nb(x))) : Nat}:
  Equal.trans(Nat, OBits.Bits.val(LLLogic.pa.nb(Nat.double(x))), Nat.double(x), Nat.double(OBits.Bits.val(LLLogic.pa.nb(x))), pa.val_nb(Nat.double(x)), Equal.cong(Nat, Nat, z => Nat.double(z), x, OBits.Bits.val(LLLogic.pa.nb(x)), Equal.sym(Nat, OBits.Bits.val(LLLogic.pa.nb(x)), x, pa.val_nb(x))))

def pa.vs_app(xs: List<&2, ONode.Node>, +y: ONode.Node) -> {LLLogic.pa.vals(OPush.starts(List.append(&2, ONode.Node, xs, [y]))) == List.append(&2, Nat, LLLogic.pa.vals(OPush.starts(xs)), [OBits.Bits.val(OFit.pair_start(y))]) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => OBits.Bits.val(OFit.pair_start(h)) <> z, LLLogic.pa.vals(OPush.starts(List.append(&2, ONode.Node, t, [y]))), List.append(&2, Nat, LLLogic.pa.vals(OPush.starts(t)), [OBits.Bits.val(OFit.pair_start(y))]), pa.vs_app(t, y))

def pa.vs_lifts(xs: List<&2, ONode.Node>) -> {LLLogic.pa.vals(OPush.starts(LLLogic.pa.lifts(xs))) == LLLogic.pa.dbls(LLLogic.pa.vals(OPush.starts(xs))) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case ONode.Node{+l, +i}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Nat.double(OBits.Bits.val(OBits.Bits.shl(l, i))) <> z, LLLogic.pa.vals(OPush.starts(LLLogic.pa.lifts(t))), LLLogic.pa.dbls(LLLogic.pa.vals(OPush.starts(t))), pa.vs_lifts(t))

# one level up, every state doubles
def pa.vst(ds: List<&2, Bool>, +j: Nat) -> {LLLogic.pa.SE(ds, 1n+j) == LLLogic.pa.dbls(LLLogic.pa.SE(ds, j)) : List<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          LLLogic.pa.cons2(OBits.Bits.val(LLLogic.pa.nb(Nat.double(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r))))), Nat.double(OBits.Bits.val(LLLogic.pa.nb(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r))))), LLLogic.pa.SE(r, 2n+j), LLLogic.pa.dbls(LLLogic.pa.SE(r, 1n+j)), pa.val_nb2(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r))), pa.vst(r, 1n+j))
        case True{}:
          LLLogic.pa.cons2(OBits.Bits.val(LLLogic.pa.nb(Nat.double(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r))))), Nat.double(OBits.Bits.val(LLLogic.pa.nb(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r))))), LLLogic.pa.SE(r, 2n+j), LLLogic.pa.dbls(LLLogic.pa.SE(r, 1n+j)), pa.val_nb2(LLLogic.pa.sh(1n+j, LLLogic.pa.B(r))), pa.vst(r, 1n+j))

# line 0 starts at 2·B(r)
def pa.vlast(d: Bool, +r: Nat) -> {OBits.Bits.val(OFit.pair_start(LLLogic.pa.line(d, r))) == Nat.double(r) : Nat}:
  match d:
    case False{}:
      pa.val_nb(Nat.double(r))
    case True{}:
      Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(LLLogic.pa.nb(r)), r, pa.val_nb(r))

def pa.sv_l(+d: Bool, +r: List<&2, Bool>, ih: {LLLogic.pa.SG(r) == LLLogic.pa.rev(LLLogic.pa.SE(r, 0n)) : List<&2, Nat>}) -> {LLLogic.pa.SG(d <> r) == List.append(&2, Nat, LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), [Nat.double(LLLogic.pa.B(r))]) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, LLLogic.pa.SG(d <> r), List.append(&2, Nat, LLLogic.pa.vals(OPush.starts(LLLogic.pa.lifts(LLLogic.pa.GV(r)))), [OBits.Bits.val(OFit.pair_start(LLLogic.pa.line(d, LLLogic.pa.B(r))))]), List.append(&2, Nat, LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), [Nat.double(LLLogic.pa.B(r))]),
    pa.vs_app(LLLogic.pa.lifts(LLLogic.pa.GV(r)), LLLogic.pa.line(d, LLLogic.pa.B(r))),
    LLList.pa.app2(LLLogic.pa.vals(OPush.starts(LLLogic.pa.lifts(LLLogic.pa.GV(r)))), LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), OBits.Bits.val(OFit.pair_start(LLLogic.pa.line(d, LLLogic.pa.B(r)))), Nat.double(LLLogic.pa.B(r)),
      Equal.trans(List<&2, Nat>, LLLogic.pa.vals(OPush.starts(LLLogic.pa.lifts(LLLogic.pa.GV(r)))), LLLogic.pa.dbls(LLLogic.pa.SG(r)), LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), pa.vs_lifts(LLLogic.pa.GV(r)), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LLLogic.pa.dbls(z), LLLogic.pa.SG(r), LLLogic.pa.rev(LLLogic.pa.SE(r, 0n)), ih)),
      pa.vlast(d, LLLogic.pa.B(r))))

def pa.sv_r(+r: List<&2, Bool>, +v1: Nat, e1: {v1 == Nat.double(LLLogic.pa.B(r)) : Nat}) -> {List.reverse.go(&2, Nat, LLLogic.pa.SE(r, 1n), [v1]) == List.append(&2, Nat, LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), [Nat.double(LLLogic.pa.B(r))]) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, List.reverse.go(&2, Nat, LLLogic.pa.SE(r, 1n), [v1]), List.append(&2, Nat, LLLogic.pa.rev(LLLogic.pa.SE(r, 1n)), [v1]), List.append(&2, Nat, LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), [Nat.double(LLLogic.pa.B(r))]),
    LLList.pa.rev_app(LLLogic.pa.SE(r, 1n), [v1]),
    LLList.pa.app2(LLLogic.pa.rev(LLLogic.pa.SE(r, 1n)), LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), v1, Nat.double(LLLogic.pa.B(r)),
      Equal.trans(List<&2, Nat>, LLLogic.pa.rev(LLLogic.pa.SE(r, 1n)), LLLogic.pa.rev(LLLogic.pa.dbls(LLLogic.pa.SE(r, 0n))), LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => LLLogic.pa.rev(z), LLLogic.pa.SE(r, 1n), LLLogic.pa.dbls(LLLogic.pa.SE(r, 0n)), pa.vst(r, 0n)), LLList.pa.dbls_rev(LLLogic.pa.SE(r, 0n), Nil{})),
      e1))

# the view's starts are push's states, oldest first
def pa.sv(ds: List<&2, Bool>) -> {LLLogic.pa.SG(ds) == LLLogic.pa.rev(LLLogic.pa.SE(ds, 0n)) : List<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          Equal.trans(List<&2, Nat>, LLLogic.pa.SG(False{} <> r), List.append(&2, Nat, LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), [Nat.double(LLLogic.pa.B(r))]), LLLogic.pa.rev(LLLogic.pa.SE(False{} <> r, 0n)), pa.sv_l(False{}, r, pa.sv(r)), Equal.sym(List<&2, Nat>, LLLogic.pa.rev(LLLogic.pa.SE(False{} <> r, 0n)), List.append(&2, Nat, LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), [Nat.double(LLLogic.pa.B(r))]), pa.sv_r(r, OBits.Bits.val(LLLogic.pa.nb(LLLogic.pa.sh(1n, LLLogic.pa.B(r)))), pa.val_nb(LLLogic.pa.sh(1n, LLLogic.pa.B(r))))))
        case True{}:
          Equal.trans(List<&2, Nat>, LLLogic.pa.SG(True{} <> r), List.append(&2, Nat, LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), [Nat.double(LLLogic.pa.B(r))]), LLLogic.pa.rev(LLLogic.pa.SE(True{} <> r, 0n)), pa.sv_l(True{}, r, pa.sv(r)), Equal.sym(List<&2, Nat>, LLLogic.pa.rev(LLLogic.pa.SE(True{} <> r, 0n)), List.append(&2, Nat, LLLogic.pa.dbls(LLLogic.pa.rev(LLLogic.pa.SE(r, 0n))), [Nat.double(LLLogic.pa.B(r))]), pa.sv_r(r, OBits.Bits.val(LLLogic.pa.nb(LLLogic.pa.sh(1n, LLLogic.pa.B(r)))), pa.val_nb(LLLogic.pa.sh(1n, LLLogic.pa.B(r))))))

def pa.same_lines(+ds: List<&2, Bool>) -> {OPush.same_lines(LLLogic.pa.GV(ds), LLLogic.pa.GE(ds, 0n)) == True{} : Bool}:
  pa.same_vals(OPush.starts(LLLogic.pa.GV(ds)), List.reverse.go(&2, List<&2, Bool>, OPush.states(LLLogic.pa.GE(ds, 0n)), Nil{}), Equal.trans(List<&2, Nat>, LLLogic.pa.SG(ds), LLLogic.pa.rev(LLLogic.pa.SE(ds, 0n)), LLLogic.pa.vals(List.reverse.go(&2, List<&2, Bool>, OPush.states(LLLogic.pa.GE(ds, 0n)), Nil{})), pa.sv(ds), Equal.sym(List<&2, Nat>, LLLogic.pa.vals(List.reverse.go(&2, List<&2, Bool>, OPush.states(LLLogic.pa.GE(ds, 0n)), Nil{})), LLLogic.pa.rev(LLLogic.pa.SE(ds, 0n)), LLList.pa.vals_rev(OPush.states(LLLogic.pa.GE(ds, 0n)), Nil{}))))

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
  -> {OFit.more_due(OFit.Last{}, t, LLLogic.pa.lift(x), LLLogic.pa.lift(c)) == OFit.more_due(OFit.Last{}, t0, x, c) : Bool}:
  match x c:
    case ONode.Node{+lx, +ix} ONode.Node{+lc, +ic}:
      %hu : {OFit.more_due.cross(_, 1n+lx, 1n+lc, False{} <> OFit.pair_end(ONode.Node{lx, ix}), False{} <> OFit.pair_end(ONode.Node{lc, ic})) == OFit.more_due(OFit.Last{}, t0, ONode.Node{lx, ix}, ONode.Node{lc, ic}) : Bool}
      pa.cross_lift(OBits.Bits.inc(t0), lx, lc, OFit.pair_end(ONode.Node{lx, ix}), OFit.pair_end(ONode.Node{lc, ic}))

def pa.vs_lift(b: Bool, -x: ONode.Node, -c: ONode.Node) -> {OFit.best.vs(b, LLLogic.pa.lift(x), LLLogic.pa.lift(c)) == LLLogic.pa.lift(OFit.best.vs(b, x, c)) : ONode.Node}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pa.take_lift(cur: Maybe<&2, ONode.Node>, +x: ONode.Node, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.best.take(OFit.Last{}, t, LLLogic.pa.lift(x), LLLogic.pa.liftm(cur)) == LLLogic.pa.liftm(OFit.best.take(OFit.Last{}, t0, x, cur)) : Maybe<&2, ONode.Node>}:
  match cur:
    case None{}:
      {==}
    case Some{+c}:
      %Equal.sym(Bool, OFit.more_due(OFit.Last{}, t, LLLogic.pa.lift(x), LLLogic.pa.lift(c)), OFit.more_due(OFit.Last{}, t0, x, c), pa.md_lift(x, c, t, t0, hu)) : {Some{OFit.best.vs(_, LLLogic.pa.lift(x), LLLogic.pa.lift(c))} == Some{LLLogic.pa.lift(OFit.best.vs(OFit.more_due(OFit.Last{}, t0, x, c), x, c))} : Maybe<&2, ONode.Node>}
      Equal.cong(ONode.Node, Maybe<&2, ONode.Node>, z => Some{z}, OFit.best.vs(OFit.more_due(OFit.Last{}, t0, x, c), LLLogic.pa.lift(x), LLLogic.pa.lift(c)), LLLogic.pa.lift(OFit.best.vs(OFit.more_due(OFit.Last{}, t0, x, c), x, c)), pa.vs_lift(OFit.more_due(OFit.Last{}, t0, x, c), x, c))

def pa.pick_lift(ok: Bool, +cur: Maybe<&2, ONode.Node>, +x: ONode.Node, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.best.pick(ok, OFit.Last{}, t, LLLogic.pa.lift(x), LLLogic.pa.liftm(cur)) == LLLogic.pa.liftm(OFit.best.pick(ok, OFit.Last{}, t0, x, cur)) : Maybe<&2, ONode.Node>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      pa.take_lift(cur, x, t, t0, hu)

# the pair of x and the next line is mergeable in up(V, z) as in V; the
# last lifted line and z never are (z is level 0)
def pa.pair_lift(v: List<&2, ONode.Node>, +x: ONode.Node, +cur: Maybe<&2, ONode.Node>, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.best.pair(OFit.Last{}, t, OInfo.All{1n}, LLLogic.pa.lift(x), List.head(&2, ONode.Node, LLLogic.pa.up(v, ONode.Node{0n, iz})), LLLogic.pa.liftm(cur)) == LLLogic.pa.liftm(OFit.best.pair(OFit.Last{}, t0, OInfo.All{1n}, x, List.head(&2, ONode.Node, v), cur)) : Maybe<&2, ONode.Node>}:
  match v x:
    case Nil{} ONode.Node{lx, ix}:
      {==}
    case ONode.Node{+ly, +iy} <> w ONode.Node{+lx, +ix}:
      pa.pick_lift(OFit.mergeable(OInfo.All{1n}, ONode.Node{lx, ix}, ONode.Node{ly, iy}), cur, ONode.Node{lx, ix}, t, t0, hu)

def pa.best_lift(v: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.best.go(OFit.Last{}, t, OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz}), LLLogic.pa.liftm(cur)) == LLLogic.pa.liftm(OFit.best.go(OFit.Last{}, t0, OInfo.All{1n}, v, cur)) : Maybe<&2, ONode.Node>}:
  match v:
    case Nil{}:
      {==}
    case +x <> +w:
      %Equal.sym(Maybe<&2, ONode.Node>, OFit.best.pair(OFit.Last{}, t, OInfo.All{1n}, LLLogic.pa.lift(x), List.head(&2, ONode.Node, LLLogic.pa.up(w, ONode.Node{0n, iz})), LLLogic.pa.liftm(cur)), LLLogic.pa.liftm(OFit.best.pair(OFit.Last{}, t0, OInfo.All{1n}, x, List.head(&2, ONode.Node, w), cur)), pa.pair_lift(w, x, cur, iz, t, t0, hu)) : {OFit.best.go(OFit.Last{}, t, OInfo.All{1n}, LLLogic.pa.up(w, ONode.Node{0n, iz}), _) == LLLogic.pa.liftm(OFit.best.go(OFit.Last{}, t0, OInfo.All{1n}, x <> w, cur)) : Maybe<&2, ONode.Node>}
      pa.best_lift(w, OFit.best.pair(OFit.Last{}, t0, OInfo.All{1n}, x, List.head(&2, ONode.Node, w), cur), iz, t, t0, hu)

def pa.mpick_lift(h: Bool, +x: ONode.Node, +y: ONode.Node, +w: List<&2, ONode.Node>, +rec: List<&2, ONode.Node>, +z: ONode.Node)
  -> {OFit.merge.pick(h, LLLogic.pa.lift(x), LLLogic.pa.lift(y), LLLogic.pa.up(w, z), LLLogic.pa.up(rec, z)) == LLLogic.pa.up(OFit.merge.pick(h, x, y, w, rec), z) : List<&2, ONode.Node>}:
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
  -> {OFit.merge.here(OInfo.All{1n}, LLLogic.pa.lift(a), LLLogic.pa.lift(x), LLLogic.pa.up(w, ONode.Node{0n, iz}), LLLogic.pa.up(OFit.merge(OInfo.All{1n}, w, a), ONode.Node{0n, iz})) == LLLogic.pa.up(OFit.merge.here(OInfo.All{1n}, a, x, w, OFit.merge(OInfo.All{1n}, w, a)), ONode.Node{0n, iz}) : List<&2, ONode.Node>}:
  match w x a:
    case Nil{} ONode.Node{+lx, +ix} ONode.Node{+la, +ia}:
      pa.mpick_nil(ONode.Node.eq(ONode.Node{lx, ix}, ONode.Node{la, ia}), ONode.Node{1n+lx, ix}, ONode.Node{0n, iz})
    case ONode.Node{+ly, +iy} <> +v ONode.Node{+lx, +ix} ONode.Node{+la, +ia}:
      pa.mpick_lift(Bool.and(ONode.Node.eq(ONode.Node{lx, ix}, ONode.Node{la, ia}), OFit.mergeable(OInfo.All{1n}, ONode.Node{lx, ix}, ONode.Node{ly, iy})), ONode.Node{lx, ix}, ONode.Node{ly, iy}, v, OFit.merge(OInfo.All{1n}, ONode.Node{ly, iy} <> v, ONode.Node{la, ia}), ONode.Node{0n, iz})

def pa.merge_lift(v: List<&2, ONode.Node>, +a: ONode.Node, +iz: List<&2, Bool>) -> {OFit.merge(OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz}), LLLogic.pa.lift(a)) == LLLogic.pa.up(OFit.merge(OInfo.All{1n}, v, a), ONode.Node{0n, iz}) : List<&2, ONode.Node>}:
  match v:
    case Nil{}:
      {==}
    case +x <> +w:
      %Equal.sym(List<&2, ONode.Node>, OFit.merge(OInfo.All{1n}, LLLogic.pa.up(w, ONode.Node{0n, iz}), LLLogic.pa.lift(a)), LLLogic.pa.up(OFit.merge(OInfo.All{1n}, w, a), ONode.Node{0n, iz}), pa.merge_lift(w, a, iz)) : {OFit.merge.here(OInfo.All{1n}, LLLogic.pa.lift(a), LLLogic.pa.lift(x), LLLogic.pa.up(w, ONode.Node{0n, iz}), _) == LLLogic.pa.up(OFit.merge(OInfo.All{1n}, x <> w, a), ONode.Node{0n, iz}) : List<&2, ONode.Node>}
      pa.here_lift(w, x, a, iz)

def pa.cif_lift(over: Bool, +v: List<&2, ONode.Node>, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.choose.if(over, OFit.Last{}, t, OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz})) == LLLogic.pa.liftm(OFit.choose.if(over, OFit.Last{}, t0, OInfo.All{1n}, v)) : Maybe<&2, ONode.Node>}:
  match over:
    case False{}:
      {==}
    case True{}:
      pa.best_lift(v, None{}, iz, t, t0, hu)

def pa.choose_lift(+v: List<&2, ONode.Node>, +b: Nat, +iz: List<&2, Bool>, -t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz})) == LLLogic.pa.liftm(OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, v)) : Maybe<&2, ONode.Node>}:
  %Equal.sym(Nat, LLLogic.pa.vs(LLLogic.pa.up(v, ONode.Node{0n, iz})), 1n+LLLogic.pa.vs(v), LLLogic.pa.size_up(v, ONode.Node{0n, iz})) : {OFit.choose.if(Nat.is_gt(_, 1n+b), OFit.Last{}, t, OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz})) == LLLogic.pa.liftm(OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, v)) : Maybe<&2, ONode.Node>}
  pa.cif_lift(Nat.is_gt(LLLogic.pa.vs(v), b), v, iz, t, t0, hu)

def pa.fit_lift(f: Nat, c: Maybe<&2, ONode.Node>, +v: List<&2, ONode.Node>, +b: Nat, +iz: List<&2, Bool>, +t: List<&2, Bool>, +t0: List<&2, Bool>, +hu: {False{} <> OBits.Bits.inc(t0) == OBits.Bits.inc(t) : List<&2, Bool>})
  -> {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(f, LLLogic.pa.liftm(c), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz}))) == LLLogic.pa.up(Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(f, c, OFit.Last{}, t0, b, 0n, OInfo.All{1n}, v)), ONode.Node{0n, iz}) : List<&2, ONode.Node>}:
  match f c:
    case 0n _:
      {==}
    case 1n+g None{}:
      {==}
    case 1n++g Some{+a}:
      +m0 = OFit.merge(OInfo.All{1n}, v, a)
      r0 = OFit.fit.go(g, OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, m0), OFit.Last{}, t0, b, 0n, OInfo.All{1n}, m0)
      %LLPair.pa.snd_cons(ONode.Node.parent(LLLogic.pa.lift(a)), OFit.fit.go(g, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, OFit.merge(OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz}), LLLogic.pa.lift(a))), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, OFit.merge(OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz}), LLLogic.pa.lift(a)))) : {_ == LLLogic.pa.up(Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.cons(ONode.Node.parent(a), r0)), ONode.Node{0n, iz}) : List<&2, ONode.Node>}
      %LLPair.pa.snd_cons(ONode.Node.parent(a), r0) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(g, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, OFit.merge(OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz}), LLLogic.pa.lift(a))), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, OFit.merge(OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz}), LLLogic.pa.lift(a)))) == LLLogic.pa.up(_, ONode.Node{0n, iz}) : List<&2, ONode.Node>}
      %Equal.sym(List<&2, ONode.Node>, OFit.merge(OInfo.All{1n}, LLLogic.pa.up(v, ONode.Node{0n, iz}), LLLogic.pa.lift(a)), LLLogic.pa.up(m0, ONode.Node{0n, iz}), pa.merge_lift(v, a, iz)) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(g, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, _), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, _)) == LLLogic.pa.up(Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r0), ONode.Node{0n, iz}) : List<&2, ONode.Node>}
      %Equal.sym(Maybe<&2, ONode.Node>, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, LLLogic.pa.up(m0, ONode.Node{0n, iz})), LLLogic.pa.liftm(OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, m0)), pa.choose_lift(m0, b, iz, t, t0, hu)) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(g, _, OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, LLLogic.pa.up(m0, ONode.Node{0n, iz}))) == LLLogic.pa.up(Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r0), ONode.Node{0n, iz}) : List<&2, ONode.Node>}
      pa.fit_lift(g, OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, m0), m0, b, iz, t, t0, hu)

def pa.good_line(d: Bool, +R: Nat) -> LLLogic.pa.Good(LLLogic.pa.line(d, R), LLLogic.pa.Bd(d, R)):
  match d:
    case False{}:
      (0n, Equal.cong(Nat, Nat, z => 3n+z, OBits.Bits.val(LLLogic.pa.nb(Nat.double(R))), Nat.double(R), pa.val_nb(Nat.double(R))))
    case True{}:
      (2n, Equal.cong(Nat, Nat, z => Nat.double(3n+z), OBits.Bits.val(LLLogic.pa.nb(R)), R, pa.val_nb(R)))

def pa.good_gv(ds: List<&2, Bool>) -> LLLogic.pa.GoodAll(LLLogic.pa.B(ds), LLLogic.pa.GV(ds)):
  match ds:
    case Nil{}:
      Unit{}
    case d <> +r:
      match d:
        case False{}:
          LLList.pa.good_app(LLLogic.pa.lifts(LLLogic.pa.GV(r)), LLLogic.pa.line(False{}, LLLogic.pa.B(r)), LLLogic.pa.Bd(False{}, LLLogic.pa.B(r)), LLNat.pa.goods_lift(False{}, LLLogic.pa.GV(r), LLLogic.pa.B(r), pa.good_gv(r)), pa.good_line(False{}, LLLogic.pa.B(r)))
        case True{}:
          LLList.pa.good_app(LLLogic.pa.lifts(LLLogic.pa.GV(r)), LLLogic.pa.line(True{}, LLLogic.pa.B(r)), LLLogic.pa.Bd(True{}, LLLogic.pa.B(r)), LLNat.pa.goods_lift(True{}, LLLogic.pa.GV(r), LLLogic.pa.B(r), pa.good_gv(r)), pa.good_line(True{}, LLLogic.pa.B(r)))

def pa.vii(+i: List<&2, Bool>) -> {OBits.Bits.val(OBits.Bits.inc(OBits.Bits.inc(i))) == 2n+OBits.Bits.val(i) : Nat}:
  Equal.trans(Nat, OBits.Bits.val(OBits.Bits.inc(OBits.Bits.inc(i))), 1n+OBits.Bits.val(OBits.Bits.inc(i)), 2n+OBits.Bits.val(i), pa.val_inc(OBits.Bits.inc(i)), LLogicNat.pa.succ(OBits.Bits.val(OBits.Bits.inc(i)), 1n+OBits.Bits.val(i), pa.val_inc(i)))

# T + 2 = 3 + 2R
def pa.vu(+R: Nat) -> {OBits.Bits.val(True{} <> OBits.Bits.inc(LLLogic.pa.nb(R))) == 3n+Nat.double(R) : Nat}:
  Equal.cong(Nat, Nat, z => 1n+Nat.double(z), OBits.Bits.val(OBits.Bits.inc(LLLogic.pa.nb(R))), 1n+R, Equal.trans(Nat, OBits.Bits.val(OBits.Bits.inc(LLLogic.pa.nb(R))), 1n+OBits.Bits.val(LLLogic.pa.nb(R)), 1n+R, pa.val_inc(LLLogic.pa.nb(R)), LLogicNat.pa.succ(OBits.Bits.val(LLLogic.pa.nb(R)), R, pa.val_nb(R))))

def pa.vX(+l: Nat, +R: Nat, +i: List<&2, Bool>)
  -> {OBits.Bits.val(OBits.Bits.add(False{} <> OBits.Bits.shl(l, True{} <> OBits.Bits.inc(LLLogic.pa.nb(R))), False{} <> OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(i))))) == Nat.add(Nat.double(LLLogic.pa.sh(l, 3n+Nat.double(R))), Nat.double(LLLogic.pa.sh(l, 2n+OBits.Bits.val(i)))) : Nat}:
  +U = {True{} <> OBits.Bits.inc(LLLogic.pa.nb(R)) : List<&2, Bool>}
  +II = OBits.Bits.inc(OBits.Bits.inc(i))
  Equal.trans(Nat, OBits.Bits.val(OBits.Bits.add(False{} <> OBits.Bits.shl(l, U), False{} <> OBits.Bits.shl(l, II))), Nat.add(Nat.double(OBits.Bits.val(OBits.Bits.shl(l, U))), Nat.double(OBits.Bits.val(OBits.Bits.shl(l, II)))), Nat.add(Nat.double(LLLogic.pa.sh(l, 3n+Nat.double(R))), Nat.double(LLLogic.pa.sh(l, 2n+OBits.Bits.val(i)))),
    pa.val_add(False{} <> OBits.Bits.shl(l, U), False{} <> OBits.Bits.shl(l, II), False{}),
    LLNat.pa.add2(Nat.double(OBits.Bits.val(OBits.Bits.shl(l, U))), Nat.double(LLLogic.pa.sh(l, 3n+Nat.double(R))), Nat.double(OBits.Bits.val(OBits.Bits.shl(l, II))), Nat.double(LLLogic.pa.sh(l, 2n+OBits.Bits.val(i))),
      Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(OBits.Bits.shl(l, U)), LLLogic.pa.sh(l, 3n+Nat.double(R)), Equal.trans(Nat, OBits.Bits.val(OBits.Bits.shl(l, U)), LLLogic.pa.sh(l, OBits.Bits.val(U)), LLLogic.pa.sh(l, 3n+Nat.double(R)), pa.val_shl(l, U), Equal.cong(Nat, Nat, z => LLLogic.pa.sh(l, z), OBits.Bits.val(U), 3n+Nat.double(R), pa.vu(R)))),
      Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(OBits.Bits.shl(l, II)), LLLogic.pa.sh(l, 2n+OBits.Bits.val(i)), Equal.trans(Nat, OBits.Bits.val(OBits.Bits.shl(l, II)), LLLogic.pa.sh(l, OBits.Bits.val(II)), LLLogic.pa.sh(l, 2n+OBits.Bits.val(i)), pa.val_shl(l, II), Equal.cong(Nat, Nat, z => LLLogic.pa.sh(l, z), OBits.Bits.val(II), 2n+OBits.Bits.val(i), pa.vii(i))))))

def pa.vY(+l: Nat, +R: Nat)
  -> {OBits.Bits.val(OBits.Bits.add(True{} <> OBits.Bits.inc(LLLogic.pa.nb(R)), False{} <> OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(LLLogic.pa.nb(Nat.double(R))))))) == Nat.add(3n+Nat.double(R), Nat.double(LLLogic.pa.sh(l, 2n+Nat.double(R)))) : Nat}:
  +U = {True{} <> OBits.Bits.inc(LLLogic.pa.nb(R)) : List<&2, Bool>}
  +PA = OBits.Bits.inc(OBits.Bits.inc(LLLogic.pa.nb(Nat.double(R))))
  Equal.trans(Nat, OBits.Bits.val(OBits.Bits.add(U, False{} <> OBits.Bits.shl(l, PA))), Nat.add(OBits.Bits.val(U), Nat.double(OBits.Bits.val(OBits.Bits.shl(l, PA)))), Nat.add(3n+Nat.double(R), Nat.double(LLLogic.pa.sh(l, 2n+Nat.double(R)))),
    pa.val_add(U, False{} <> OBits.Bits.shl(l, PA), False{}),
    LLNat.pa.add2(OBits.Bits.val(U), 3n+Nat.double(R), Nat.double(OBits.Bits.val(OBits.Bits.shl(l, PA))), Nat.double(LLLogic.pa.sh(l, 2n+Nat.double(R))),
      pa.vu(R),
      Equal.cong(Nat, Nat, z => Nat.double(z), OBits.Bits.val(OBits.Bits.shl(l, PA)), LLLogic.pa.sh(l, 2n+Nat.double(R)), Equal.trans(Nat, OBits.Bits.val(OBits.Bits.shl(l, PA)), LLLogic.pa.sh(l, OBits.Bits.val(PA)), LLLogic.pa.sh(l, 2n+Nat.double(R)), pa.val_shl(l, PA), Equal.cong(Nat, Nat, z => LLLogic.pa.sh(l, z), OBits.Bits.val(PA), 2n+Nat.double(R), Equal.trans(Nat, OBits.Bits.val(PA), 2n+OBits.Bits.val(LLLogic.pa.nb(Nat.double(R))), 2n+Nat.double(R), pa.vii(LLLogic.pa.nb(Nat.double(R))), Equal.cong(Nat, Nat, z => 2n+z, OBits.Bits.val(LLLogic.pa.nb(Nat.double(R))), Nat.double(R), pa.val_nb(Nat.double(R)))))))))

# the pair (a0, b0) is more due than a lifted line of the view of R
def pa.old_one(c: ONode.Node, +R: Nat, g: LLLogic.pa.Good(c, R)) -> {OFit.more_due(OFit.Last{}, LLLogic.pa.tb0(R), LLLogic.pa.a0(R), LLLogic.pa.lift(c)) == True{} : Bool}:
  match c:
    case ONode.Node{+l, +i}:
      (k0, e) = g
      +k = k0
      +U = {True{} <> OBits.Bits.inc(LLLogic.pa.nb(R)) : List<&2, Bool>}
      +X = OBits.Bits.add(False{} <> OBits.Bits.shl(l, U), False{} <> OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(i))))
      +Y = OBits.Bits.add(U, False{} <> OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(LLLogic.pa.nb(Nat.double(R))))))
      -XX = Nat.add(Nat.double(LLLogic.pa.sh(l, 3n+Nat.double(R))), Nat.double(LLLogic.pa.sh(l, 2n+OBits.Bits.val(i))))
      +YY = Nat.add(3n+Nat.double(R), Nat.double(LLLogic.pa.sh(l, 2n+Nat.double(R))))
      pa.gt_val(X, Y, LLNat.pa.old_one.gt(X, Y, XX, YY, k, pa.vX(l, R, i), pa.vY(l, R), LLNat.pa.ineq(l, R, OBits.Bits.val(i), k, e)))

def pa.eq_lift0(c: ONode.Node, -ia: List<&2, Bool>) -> {ONode.Node.eq(LLLogic.pa.lift(c), ONode.Node{0n, ia}) == False{} : Bool}:
  match c:
    case ONode.Node{l, i}:
      {==}

def pa.pre_lifts(xs: List<&2, ONode.Node>, +R: Nat, g: LLLogic.pa.GoodAll(R, xs)) -> LLLogic.pa.PreAll(LLLogic.pa.tb0(R), LLLogic.pa.a0(R), LLLogic.pa.lifts(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case +c <> t:
      (gc, gt) = g
      ((pa.old_one(c, R, gc), pa.eq_lift0(c, LLLogic.pa.nb(Nat.double(R)))), pa.pre_lifts(t, R, gt))

def pa.oldm_vs(b: Bool, -t: List<&2, Bool>, -a: ONode.Node, -x: ONode.Node, -c: ONode.Node, ox: {OFit.more_due(OFit.Last{}, t, a, x) == True{} : Bool}, oc: {OFit.more_due(OFit.Last{}, t, a, c) == True{} : Bool})
  -> LLLogic.pa.OldM(t, a, Some{OFit.best.vs(b, x, c)}):
  match b:
    case True{}:
      ox
    case False{}:
      oc

def pa.oldm_take(cur: Maybe<&2, ONode.Node>, +t: List<&2, Bool>, -a: ONode.Node, +x: ONode.Node, ox: {OFit.more_due(OFit.Last{}, t, a, x) == True{} : Bool}, oc: LLLogic.pa.OldM(t, a, cur))
  -> LLLogic.pa.OldM(t, a, OFit.best.take(OFit.Last{}, t, x, cur)):
  match cur:
    case None{}:
      ox
    case Some{+c}:
      pa.oldm_vs(OFit.more_due(OFit.Last{}, t, x, c), t, a, x, c, ox, oc)

def pa.oldm_pick(ok: Bool, +cur: Maybe<&2, ONode.Node>, +t: List<&2, Bool>, -a: ONode.Node, +x: ONode.Node, ox: {OFit.more_due(OFit.Last{}, t, a, x) == True{} : Bool}, oc: LLLogic.pa.OldM(t, a, cur))
  -> LLLogic.pa.OldM(t, a, OFit.best.pick(ok, OFit.Last{}, t, x, cur)):
  match ok:
    case False{}:
      oc
    case True{}:
      pa.oldm_take(cur, t, a, x, ox, oc)

def pa.oldm_pair(nxt: Maybe<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +t: List<&2, Bool>, -a: ONode.Node, +x: ONode.Node, ox: {OFit.more_due(OFit.Last{}, t, a, x) == True{} : Bool}, oc: LLLogic.pa.OldM(t, a, cur))
  -> LLLogic.pa.OldM(t, a, OFit.best.pair(OFit.Last{}, t, OInfo.All{1n}, x, nxt, cur)):
  match nxt:
    case None{}:
      oc
    case Some{+y}:
      pa.oldm_pick(OFit.mergeable(OInfo.All{1n}, x, y), cur, t, a, x, ox, oc)

def pa.take_base(cur: Maybe<&2, ONode.Node>, +t: List<&2, Bool>, +a: ONode.Node, +b: ONode.Node, oc: LLLogic.pa.OldM(t, a, cur))
  -> {OFit.best.go(OFit.Last{}, t, OInfo.All{1n}, [b], OFit.best.take(OFit.Last{}, t, a, cur)) == Some{a} : Maybe<&2, ONode.Node>}:
  match cur:
    case None{}:
      {==}
    case Some{+c}:
      %Equal.sym(Bool, OFit.more_due(OFit.Last{}, t, a, c), True{}, oc) : {OFit.best.go(OFit.Last{}, t, OInfo.All{1n}, [b], Some{OFit.best.vs(_, a, c)}) == Some{a} : Maybe<&2, ONode.Node>}
      {==}

# best picks a when (a, b) may merge, comes last, and beats every line
# before it
def pa.best_base(xs: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +t: List<&2, Bool>, +a: ONode.Node, +b: ONode.Node, +mab: {OFit.mergeable(OInfo.All{1n}, a, b) == True{} : Bool}, pre: LLLogic.pa.PreAll(t, a, xs), oc: LLLogic.pa.OldM(t, a, cur))
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
def pa.merge_base(xs: List<&2, ONode.Node>, +a: ONode.Node, +b: ONode.Node, +mab: {OFit.mergeable(OInfo.All{1n}, a, b) == True{} : Bool}, -t: List<&2, Bool>, pre: LLLogic.pa.PreAll(t, a, xs))
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

def pa.mab(+R: Nat) -> {OFit.mergeable(OInfo.All{1n}, LLLogic.pa.a0(R), LLLogic.pa.b0(R)) == True{} : Bool}:
  %Equal.sym(Bool, OBits.Bits.low(LLLogic.pa.nb(Nat.double(R))), False{}, pa.low_even(R)) : {Bool.and(Bool.and(Bool.not(_), OBits.Bits.eq(OBits.Bits.up(LLLogic.pa.nb(Nat.double(R))), LLLogic.pa.nb(R))), True{}) == True{} : Bool}
  %Equal.sym(List<&2, Bool>, OBits.Bits.up(LLLogic.pa.nb(Nat.double(R))), LLLogic.pa.nb(R), pa.up_even(R)) : {Bool.and(OBits.Bits.eq(_, LLLogic.pa.nb(R)), True{}) == True{} : Bool}
  %Equal.sym(Bool, OBits.Bits.eq(LLLogic.pa.nb(R), LLLogic.pa.nb(R)), True{}, pa.bits_eq_self(LLLogic.pa.nb(R))) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def pa.hc_base(+r: List<&2, Bool>)
  -> {OFit.choose(OFit.Last{}, LLLogic.pa.tb0(LLLogic.pa.B(r)), 1n+List.length(&2, Bool, r), 0n, OInfo.All{1n}, List.append(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r)), [LLLogic.pa.a0(LLLogic.pa.B(r)), LLLogic.pa.b0(LLLogic.pa.B(r))])) == Some{LLLogic.pa.a0(LLLogic.pa.B(r))} : Maybe<&2, ONode.Node>}:
  +R = LLLogic.pa.B(r)
  +y = List.append(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r)), [LLLogic.pa.a0(R), LLLogic.pa.b0(R)])
  %Equal.sym(Nat, LLLogic.pa.vs(y), 2n+List.length(&2, Bool, r), LLList.pa.size_hi(r, [LLLogic.pa.a0(R), LLLogic.pa.b0(R)])) : {OFit.choose.if(Nat.is_gt(_, 1n+List.length(&2, Bool, r)), OFit.Last{}, LLLogic.pa.tb0(R), OInfo.All{1n}, y) == Some{LLLogic.pa.a0(R)} : Maybe<&2, ONode.Node>}
  %Equal.sym(Bool, Nat.is_gt(1n+List.length(&2, Bool, r), List.length(&2, Bool, r)), True{}, LLNat.pa.gt_succ(List.length(&2, Bool, r))) : {OFit.choose.if(_, OFit.Last{}, LLLogic.pa.tb0(R), OInfo.All{1n}, y) == Some{LLLogic.pa.a0(R)} : Maybe<&2, ONode.Node>}
  pa.best_base(LLLogic.pa.lifts(LLLogic.pa.GV(r)), None{}, LLLogic.pa.tb0(R), LLLogic.pa.a0(R), LLLogic.pa.b0(R), pa.mab(R), pa.pre_lifts(LLLogic.pa.GV(r), R, pa.good_gv(r)), Unit{})

def pa.hm_base(+r: List<&2, Bool>)
  -> {OFit.merge(OInfo.All{1n}, List.append(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r)), [LLLogic.pa.a0(LLLogic.pa.B(r)), LLLogic.pa.b0(LLLogic.pa.B(r))]), LLLogic.pa.a0(LLLogic.pa.B(r))) == LLLogic.pa.GV(True{} <> r) : List<&2, ONode.Node>}:
  +R = LLLogic.pa.B(r)
  Equal.trans(List<&2, ONode.Node>, OFit.merge(OInfo.All{1n}, List.append(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r)), [LLLogic.pa.a0(R), LLLogic.pa.b0(R)]), LLLogic.pa.a0(R)), List.append(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r)), [ONode.Node.parent(LLLogic.pa.a0(R))]), LLLogic.pa.GV(True{} <> r),
    pa.merge_base(LLLogic.pa.lifts(LLLogic.pa.GV(r)), LLLogic.pa.a0(R), LLLogic.pa.b0(R), pa.mab(R), LLLogic.pa.tb0(R), pa.pre_lifts(LLLogic.pa.GV(r), R, pa.good_gv(r))),
    Equal.cong(List<&2, Bool>, List<&2, ONode.Node>, z => List.append(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r)), [ONode.Node{1n, z}]), OBits.Bits.up(LLLogic.pa.nb(Nat.double(R))), LLLogic.pa.nb(R), pa.up_even(R)))

def pa.hn_base(+r: List<&2, Bool>)
  -> {OFit.choose(OFit.Last{}, LLLogic.pa.tb0(LLLogic.pa.B(r)), 1n+List.length(&2, Bool, r), 0n, OInfo.All{1n}, LLLogic.pa.GV(True{} <> r)) == None{} : Maybe<&2, ONode.Node>}:
  +R = LLLogic.pa.B(r)
  %Equal.sym(Nat, LLLogic.pa.vs(LLLogic.pa.GV(True{} <> r)), 1n+List.length(&2, Bool, r), LLList.pa.size_hi(r, [ONode.Node{1n, LLLogic.pa.nb(R)}])) : {OFit.choose.if(Nat.is_gt(_, 1n+List.length(&2, Bool, r)), OFit.Last{}, LLLogic.pa.tb0(R), OInfo.All{1n}, LLLogic.pa.GV(True{} <> r)) == None{} : Maybe<&2, ONode.Node>}
  %Equal.sym(Bool, Nat.is_gt(1n+List.length(&2, Bool, r), 1n+List.length(&2, Bool, r)), False{}, LLNat.pa.gt_self(1n+List.length(&2, Bool, r))) : {OFit.choose.if(_, OFit.Last{}, LLLogic.pa.tb0(R), OInfo.All{1n}, LLLogic.pa.GV(True{} <> r)) == None{} : Maybe<&2, ONode.Node>}
  {==}

# lowest digit 0: the new line merges with line 0
def pa.F_base(+r: List<&2, Bool>, +f: Nat) -> LLLogic.pa.FT(False{} <> r, f):
  +R = LLLogic.pa.B(r)
  +X = LLLogic.pa.lifts(LLLogic.pa.GV(r))
  +n = {1n+List.length(&2, Bool, r) : Nat}
  %Equal.sym(List<&2, Bool>, LLLogic.pa.nb(1n+Nat.double(R)), True{} <> LLLogic.pa.nb(R), LLNat.pa.nb_odd(R)) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, OFit.choose(OFit.Last{}, OBits.Bits.inc(_), n, 0n, OInfo.All{1n}, List.append(&2, ONode.Node, List.append(&2, ONode.Node, X, [LLLogic.pa.a0(R)]), [ONode.Node{0n, _}])), OFit.Last{}, OBits.Bits.inc(_), n, 0n, OInfo.All{1n}, List.append(&2, ONode.Node, List.append(&2, ONode.Node, X, [LLLogic.pa.a0(R)]), [ONode.Node{0n, _}]))) == LLLogic.pa.GV(True{} <> r) : List<&2, ONode.Node>}
  %Equal.sym(List<&2, ONode.Node>, List.append(&2, ONode.Node, List.append(&2, ONode.Node, X, [LLLogic.pa.a0(R)]), [LLLogic.pa.b0(R)]), List.append(&2, ONode.Node, X, [LLLogic.pa.a0(R), LLLogic.pa.b0(R)]), LLList.pa.app_ab(X, LLLogic.pa.a0(R), LLLogic.pa.b0(R))) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, OFit.choose(OFit.Last{}, LLLogic.pa.tb0(R), n, 0n, OInfo.All{1n}, _), OFit.Last{}, LLLogic.pa.tb0(R), n, 0n, OInfo.All{1n}, _)) == LLLogic.pa.GV(True{} <> r) : List<&2, ONode.Node>}
  LLPair.pa.base_fit(f, List.append(&2, ONode.Node, X, [LLLogic.pa.a0(R), LLLogic.pa.b0(R)]), LLLogic.pa.a0(R), LLLogic.pa.GV(True{} <> r), LLLogic.pa.tb0(R), n, pa.hc_base(r), pa.hm_base(r), pa.hn_base(r))

# lowest digit 1: the step is the lifted step of the higher digits
def pa.F_lift(+r: List<&2, Bool>, +f: Nat, ih: LLLogic.pa.FT(r, f)) -> LLLogic.pa.FT(True{} <> r, f):
  +R = LLLogic.pa.B(r)
  +iz = LLLogic.pa.nb(2n+Nat.double(R))
  +t = LLLogic.pa.T2(True{} <> r)
  +t0 = LLLogic.pa.T2(r)
  +b = LLLogic.pa.bud(r)
  +c0 = OFit.choose(OFit.Last{}, t0, b, 0n, OInfo.All{1n}, LLLogic.pa.V(r))
  +hu = Equal.sym(List<&2, Bool>, OBits.Bits.inc(OBits.Bits.inc(LLLogic.pa.nb(2n+Nat.double(R)))), OBits.Bits.inc(OBits.Bits.inc(False{} <> LLLogic.pa.nb(1n+R))), Equal.cong(List<&2, Bool>, List<&2, Bool>, z => OBits.Bits.inc(OBits.Bits.inc(z)), LLLogic.pa.nb(2n+Nat.double(R)), False{} <> LLLogic.pa.nb(1n+R), LLNat.pa.nb_even(R)))
  %Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, w => List.append(&2, ONode.Node, w, [ONode.Node{0n, iz}]), LLLogic.pa.lifts(List.append(&2, ONode.Node, LLLogic.pa.GV(r), [ONode.Node{0n, LLLogic.pa.nb(R)}])), List.append(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r)), [LLLogic.pa.lift(ONode.Node{0n, LLLogic.pa.nb(R)})]), LLList.pa.lifts_app1(LLLogic.pa.GV(r), ONode.Node{0n, LLLogic.pa.nb(R)})) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, _), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, _)) == LLLogic.pa.GV(False{} <> LLLogic.pa.inc(r)) : List<&2, ONode.Node>}
  %Equal.sym(Maybe<&2, ONode.Node>, OFit.choose(OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, LLLogic.pa.up(LLLogic.pa.V(r), ONode.Node{0n, iz})), LLLogic.pa.liftm(c0), pa.choose_lift(LLLogic.pa.V(r), b, iz, t, t0, hu)) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, _, OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, LLLogic.pa.up(LLLogic.pa.V(r), ONode.Node{0n, iz}))) == LLLogic.pa.GV(False{} <> LLLogic.pa.inc(r)) : List<&2, ONode.Node>}
  -S0 = Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, c0, OFit.Last{}, t0, b, 0n, OInfo.All{1n}, LLLogic.pa.V(r)))
  Equal.trans(List<&2, ONode.Node>, Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, LLLogic.pa.liftm(c0), OFit.Last{}, t, 1n+b, 0n, OInfo.All{1n}, LLLogic.pa.up(LLLogic.pa.V(r), ONode.Node{0n, iz}))), LLLogic.pa.up(S0, ONode.Node{0n, iz}), LLLogic.pa.GV(False{} <> LLLogic.pa.inc(r)),
    pa.fit_lift(1n+f, c0, LLLogic.pa.V(r), b, iz, t, t0, hu),
    Equal.trans(List<&2, ONode.Node>, LLLogic.pa.up(S0, ONode.Node{0n, iz}), LLLogic.pa.up(LLLogic.pa.GV(LLLogic.pa.inc(r)), ONode.Node{0n, iz}), LLLogic.pa.GV(False{} <> LLLogic.pa.inc(r)),
      Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, w => LLLogic.pa.up(w, ONode.Node{0n, iz}), S0, LLLogic.pa.GV(LLLogic.pa.inc(r)), ih),
      Equal.cong(Nat, List<&2, ONode.Node>, w => List.append(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(LLLogic.pa.inc(r))), [ONode.Node{0n, LLLogic.pa.nb(Nat.double(w))}]), 1n+R, LLLogic.pa.B(LLLogic.pa.inc(r)), Equal.sym(Nat, LLLogic.pa.B(LLLogic.pa.inc(r)), 1n+R, LLLogic.pa.B_inc(r)))))

def pa.F(ds: List<&2, Bool>, +f: Nat) -> LLLogic.pa.FT(ds, f):
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
def pa.step(+ds: List<&2, Bool>) -> {OFit.fit.view(OFit.Last{}, LLLogic.pa.T2(ds), List.length(&2, OPush.Entry, LLLogic.pa.GE(LLLogic.pa.inc(ds), 0n)), 0n, OInfo.All{1n}, LLLogic.pa.V(ds)) == LLLogic.pa.GV(LLLogic.pa.inc(ds)) : List<&2, ONode.Node>}:
  %Equal.sym(Nat, List.length(&2, OPush.Entry, LLLogic.pa.GE(LLLogic.pa.inc(ds), 0n)), LLLogic.pa.bud(ds), LLList.pa.len_GE(LLLogic.pa.inc(ds), 0n)) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(List.length(&2, ONode.Node, LLLogic.pa.V(ds)), OFit.choose(OFit.Last{}, LLLogic.pa.T2(ds), _, 0n, OInfo.All{1n}, LLLogic.pa.V(ds)), OFit.Last{}, LLLogic.pa.T2(ds), _, 0n, OInfo.All{1n}, LLLogic.pa.V(ds))) == LLLogic.pa.GV(LLLogic.pa.inc(ds)) : List<&2, ONode.Node>}
  %Equal.sym(Nat, List.length(&2, ONode.Node, LLLogic.pa.V(ds)), 1n+List.length(&2, ONode.Node, LLLogic.pa.GV(ds)), LLList.pa.len_app1(LLLogic.pa.GV(ds), ONode.Node.leaf(LLLogic.pa.nb(LLLogic.pa.B(ds))))) : {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(_, OFit.choose(OFit.Last{}, LLLogic.pa.T2(ds), LLLogic.pa.bud(ds), 0n, OInfo.All{1n}, LLLogic.pa.V(ds)), OFit.Last{}, LLLogic.pa.T2(ds), LLLogic.pa.bud(ds), 0n, OInfo.All{1n}, LLLogic.pa.V(ds))) == LLLogic.pa.GV(LLLogic.pa.inc(ds)) : List<&2, ONode.Node>}
  pa.F(ds, List.length(&2, ONode.Node, LLLogic.pa.GV(ds)))

# The law
# -------

def pa.agree(n: Nat, +ds: List<&2, Bool>) -> {OPush.agree.go(n, OFit.Last{}, LLLogic.pa.nb(LLLogic.pa.B(ds)), LLLogic.pa.GE(ds, 0n), LLLogic.pa.GV(ds)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +es2 = LLLogic.pa.GE(LLLogic.pa.inc(ds), 0n)
      +v2 = LLLogic.pa.GV(LLLogic.pa.inc(ds))
      %Equal.sym(List<&2, OPush.Entry>, OPush.push(LLLogic.pa.GE(ds, 0n), LLLogic.pa.nb(LLLogic.pa.B(ds))), es2, pa.push_ge(ds, 0n)) : {Bool.and(OPush.same_lines(OFit.fit.view(OFit.Last{}, LLLogic.pa.T2(ds), List.length(&2, OPush.Entry, _), 0n, OInfo.All{1n}, LLLogic.pa.V(ds)), _), OPush.agree.go(p, OFit.Last{}, LLLogic.pa.T2(ds), _, OFit.fit.view(OFit.Last{}, LLLogic.pa.T2(ds), List.length(&2, OPush.Entry, _), 0n, OInfo.All{1n}, LLLogic.pa.V(ds)))) == True{} : Bool}
      %Equal.sym(List<&2, ONode.Node>, OFit.fit.view(OFit.Last{}, LLLogic.pa.T2(ds), List.length(&2, OPush.Entry, es2), 0n, OInfo.All{1n}, LLLogic.pa.V(ds)), v2, pa.step(ds)) : {Bool.and(OPush.same_lines(_, es2), OPush.agree.go(p, OFit.Last{}, LLLogic.pa.T2(ds), es2, _)) == True{} : Bool}
      %LLLogic.pa.B_inc(ds) : {Bool.and(OPush.same_lines(v2, es2), OPush.agree.go(p, OFit.Last{}, LLLogic.pa.nb(_), es2, v2)) == True{} : Bool}
      %Equal.sym(Bool, OPush.same_lines(v2, es2), True{}, pa.same_lines(LLLogic.pa.inc(ds))) : {Bool.and(_, OPush.agree.go(p, OFit.Last{}, LLLogic.pa.nb(LLLogic.pa.B(LLLogic.pa.inc(ds))), es2, v2)) == True{} : Bool}
      pa.agree(p, LLLogic.pa.inc(ds))

def push_agrees_always(n: Nat) -> {OPush.agree(OFit.Last{}, n) == True{} : Bool}:
  pa.agree(n, Nil{})
