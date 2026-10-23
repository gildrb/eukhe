# eukhe: lemmas of the proof of LAW push_agrees_always: list

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/fit.bend as OFit
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/push.bend as OPush
import ../../base/nat/add.bend as LNatAdd
import ../../base/nat/misc.bend as LNatMisc
import ./nat.bend as LLNat

# A number's bits
# ---------------
# nb(n): n in binary without high zero bits, as Bits.inc counts

def pa.nb(n: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      OBits.Bits.inc(pa.nb(p))

def pa.nb_odd(+r: Nat) -> {pa.nb(1n+Nat.double(r)) == True{} <> pa.nb(r) : List<&2, Bool>}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, z => OBits.Bits.inc(OBits.Bits.inc(z)), pa.nb(1n+Nat.double(p)), True{} <> pa.nb(p), pa.nb_odd(p))

def pa.nb_even(+p: Nat) -> {pa.nb(2n+Nat.double(p)) == False{} <> pa.nb(1n+p) : List<&2, Bool>}:
  Equal.cong(List<&2, Bool>, List<&2, Bool>, z => OBits.Bits.inc(z), pa.nb(1n+Nat.double(p)), True{} <> pa.nb(p), pa.nb_odd(p))

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

def pa.B_inc(ds: List<&2, Bool>) -> {LLNat.pa.B(pa.inc(ds)) == 1n+LLNat.pa.B(ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          {==}
        case True{}:
          Equal.cong(Nat, Nat, z => 1n+Nat.double(z), LLNat.pa.B(pa.inc(r)), 1n+LLNat.pa.B(r), pa.B_inc(r))

# push's list (newest first) at offset j: entry j keeps its digit and
# holds the state where its line starts, sum over k > j of (1 + d_k)·2^k
def pa.GE(ds: List<&2, Bool>, +j: Nat) -> List<&2, OPush.Entry>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> +r:
      match d:
        case False{}:
          OPush.Entry{0n, 0n, pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(r)))} <> pa.GE(r, 1n+j)
        case True{}:
          OPush.Entry{1n, 0n, pa.nb(LLNat.pa.sh(1n+j, LLNat.pa.B(r)))} <> pa.GE(r, 1n+j)

# Push's list is the view
# -----------------------
# Compared by value: the view's starts and push's states, oldest first.

def pa.vals(xs: List<&2, List<&2, Bool>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      OBits.Bits.val(h) <> pa.vals(t)

def pa.dbls(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      Nat.double(h) <> pa.dbls(t)

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

def pa.SE(ds: List<&2, Bool>, +j: Nat) -> List<&2, Nat>:
  pa.vals(OPush.states(pa.GE(ds, j)))

def pa.cons2(-a: Nat, -b: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>, ea: {a == b : Nat}, et: {xs == ys : List<&2, Nat>}) -> {a <> xs == b <> ys : List<&2, Nat>}:
  %ea : {a <> xs == _ <> ys : List<&2, Nat>}
  %et : {a <> xs == a <> _ : List<&2, Nat>}
  {==}

def pa.rev(xs: List<&2, Nat>) -> List<&2, Nat>:
  List.reverse.go(&2, Nat, xs, Nil{})

def pa.app2(-xs: List<&2, Nat>, -ys: List<&2, Nat>, -a: Nat, -b: Nat, et: {xs == ys : List<&2, Nat>}, ea: {a == b : Nat}) -> {List.append(&2, Nat, xs, [a]) == List.append(&2, Nat, ys, [b]) : List<&2, Nat>}:
  %et : {List.append(&2, Nat, xs, [a]) == List.append(&2, Nat, _, [b]) : List<&2, Nat>}
  %ea : {List.append(&2, Nat, xs, [a]) == List.append(&2, Nat, xs, [_]) : List<&2, Nat>}
  {==}

def pa.len_GE(ds: List<&2, Bool>, +j: Nat) -> {List.length(&2, OPush.Entry, pa.GE(ds, j)) == List.length(&2, Bool, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          LNatMisc.pa.succ(List.length(&2, OPush.Entry, pa.GE(r, 1n+j)), List.length(&2, Bool, r), pa.len_GE(r, 1n+j))
        case True{}:
          LNatMisc.pa.succ(List.length(&2, OPush.Entry, pa.GE(r, 1n+j)), List.length(&2, Bool, r), pa.len_GE(r, 1n+j))

def pa.len_app1(xs: List<&2, ONode.Node>, -y: ONode.Node) -> {List.length(&2, ONode.Node, List.append(&2, ONode.Node, xs, [y])) == 1n+List.length(&2, ONode.Node, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      LNatMisc.pa.succ(List.length(&2, ONode.Node, List.append(&2, ONode.Node, t, [y])), 1n+List.length(&2, ONode.Node, t), pa.len_app1(t, y))

def pa.size_app(xs: List<&2, ONode.Node>, +ys: List<&2, ONode.Node>) -> {LLNat.pa.vs(List.append(&2, ONode.Node, xs, ys)) == Nat.add(LLNat.pa.vs(ys), List.length(&2, ONode.Node, xs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(LLNat.pa.vs(ys), 0n), LLNat.pa.vs(ys), LNatAdd.pa.add_zero(LLNat.pa.vs(ys)))
    case h <> +t:
      Equal.trans(Nat, 1n+LLNat.pa.vs(List.append(&2, ONode.Node, t, ys)), 1n+Nat.add(LLNat.pa.vs(ys), List.length(&2, ONode.Node, t)), Nat.add(LLNat.pa.vs(ys), 1n+List.length(&2, ONode.Node, t)),
        LNatMisc.pa.succ(LLNat.pa.vs(List.append(&2, ONode.Node, t, ys)), Nat.add(LLNat.pa.vs(ys), List.length(&2, ONode.Node, t)), pa.size_app(t, ys)),
        Equal.sym(Nat, Nat.add(LLNat.pa.vs(ys), 1n+List.length(&2, ONode.Node, t)), 1n+Nat.add(LLNat.pa.vs(ys), List.length(&2, ONode.Node, t)), LNatAdd.pa.add_succ(LLNat.pa.vs(ys), List.length(&2, ONode.Node, t))))

# T + 1 in binary, T = 1 + 2R
def pa.tb0(+R: Nat) -> List<&2, Bool>:
  OBits.Bits.inc(True{} <> pa.nb(R))

# Pre(t, a, x): the pair from a is more due than x, and x is not a
def pa.Pre(+t: List<&2, Bool>, +a: ONode.Node, +x: ONode.Node) -> Type:
  ({OFit.more_due(OFit.Last{}, t, a, x) == True{} : Bool} & {ONode.Node.eq(x, a) == False{} : Bool})

def pa.PreAll(+t: List<&2, Bool>, +a: ONode.Node, xs: List<&2, ONode.Node>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +x <> r:
      (pa.Pre(t, a, x) & pa.PreAll(t, a, r))

# the best so far, if any, is less due than the pair from a
def pa.OldM(+t: List<&2, Bool>, +a: ONode.Node, m: Maybe<&2, ONode.Node>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{c}:
      {OFit.more_due(OFit.Last{}, t, a, c) == True{} : Bool}

def pa.app_ab(xs: List<&2, ONode.Node>, +a: ONode.Node, +b: ONode.Node) -> {List.append(&2, ONode.Node, List.append(&2, ONode.Node, xs, [a]), [b]) == List.append(&2, ONode.Node, xs, [a, b]) : List<&2, ONode.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, z => h <> z, List.append(&2, ONode.Node, List.append(&2, ONode.Node, t, [a]), [b]), List.append(&2, ONode.Node, t, [a, b]), pa.app_ab(t, a, b))

# T + 1, the view with message T's line, and the budget push gives
def pa.T2(+ds: List<&2, Bool>) -> List<&2, Bool>:
  OBits.Bits.inc(pa.nb(LLNat.pa.B(ds)))

def pa.bud(+ds: List<&2, Bool>) -> Nat:
  List.length(&2, Bool, pa.inc(ds))
