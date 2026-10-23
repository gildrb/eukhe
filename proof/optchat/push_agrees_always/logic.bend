# eukhe: lemmas of the proof of LAW push_agrees_always: logic

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/fit.bend as OFit
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/push.bend as OPush
import ../../base/logic/nat.bend as LLogicNat

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

def pa.hd(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      h

# Sizes
# -----
# Under push every line counts 1 and every node is built (All{1}).

def pa.vs(v: List<&2, ONode.Node>) -> Nat:
  OFit.view_size(0n, OInfo.All{1n}, v)

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

# A number's bits
# ---------------
# nb(n): n in binary without high zero bits, as Bits.inc counts

def pa.nb(n: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      OBits.Bits.inc(pa.nb(p))

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
def pa.GE(ds: List<&2, Bool>, +j: Nat) -> List<&2, OPush.Entry>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> +r:
      match d:
        case False{}:
          OPush.Entry{0n, 0n, pa.nb(pa.sh(1n+j, pa.B(r)))} <> pa.GE(r, 1n+j)
        case True{}:
          OPush.Entry{1n, 0n, pa.nb(pa.sh(1n+j, pa.B(r)))} <> pa.GE(r, 1n+j)

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

def pa.SE(ds: List<&2, Bool>, +j: Nat) -> List<&2, Nat>:
  pa.vals(OPush.states(pa.GE(ds, j)))

def pa.cons2(-a: Nat, -b: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>, ea: {a == b : Nat}, et: {xs == ys : List<&2, Nat>}) -> {a <> xs == b <> ys : List<&2, Nat>}:
  %ea : {a <> xs == _ <> ys : List<&2, Nat>}
  %et : {a <> xs == a <> _ : List<&2, Nat>}
  {==}

def pa.rev(xs: List<&2, Nat>) -> List<&2, Nat>:
  List.reverse.go(&2, Nat, xs, Nil{})

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

# T + 1, the view with message T's line, and the budget push gives
def pa.T2(+ds: List<&2, Bool>) -> List<&2, Bool>:
  OBits.Bits.inc(pa.nb(pa.B(ds)))

def pa.bud(+ds: List<&2, Bool>) -> Nat:
  List.length(&2, Bool, pa.inc(ds))

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
      ONode.Node{0n, pa.nb(Nat.double(r))}
    case True{}:
      ONode.Node{1n, pa.nb(r)}

def pa.GV(ds: List<&2, Bool>) -> List<&2, ONode.Node>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> +r:
      List.append(&2, ONode.Node, pa.lifts(pa.GV(r)), [pa.line(d, pa.B(r))])

def pa.SG(ds: List<&2, Bool>) -> List<&2, Nat>:
  pa.vals(OPush.starts(pa.GV(ds)))

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

def pa.size_up(v: List<&2, ONode.Node>, +z: ONode.Node) -> {pa.vs(pa.up(v, z)) == 1n+pa.vs(v) : Nat}:
  match v:
    case Nil{}:
      {==}
    case h <> w:
      LLogicNat.pa.succ(pa.vs(pa.up(w, z)), 1n+pa.vs(w), pa.size_up(w, z))

# Older lines end late enough
# ---------------------------
# Good(c, R): line c = node(l, i) of the view of R messages has
# (i + 3)·2^l >= R + 2, i.e. it ends at most 2^(l+1) - 2 messages before
# R: what follows it is at most two lines per lower level.

def pa.Good(c: ONode.Node, +R: Nat) -> Type:
  match c:
    case ONode.Node{l, i}:
      &k:Nat -> {pa.sh(l, 3n+OBits.Bits.val(i)) == Nat.add(k, 2n+R) : Nat}

def pa.GoodAll(+R: Nat, xs: List<&2, ONode.Node>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case c <> t:
      (pa.Good(c, R) & pa.GoodAll(R, t))

# The newest pair is the most due
# -------------------------------
# With the lowest digit 0, T = 1 + 2R: line 0 is a0 = node(0, 2R), the new
# line b0 = node(0, 2R + 1), and the pair is due (T - last)/1 = 1. The
# older lines are the view of R lifted, each due less than 1 by Good:
# in the cross form, 2^l·(T + 2) + e_c > (T + 2) + 2^l·e_a.

def pa.a0(+R: Nat) -> ONode.Node:
  ONode.Node{0n, pa.nb(Nat.double(R))}

def pa.b0(+R: Nat) -> ONode.Node:
  ONode.Node{0n, True{} <> pa.nb(R)}

def pa.V(+ds: List<&2, Bool>) -> List<&2, ONode.Node>:
  List.append(&2, ONode.Node, pa.GV(ds), [ONode.Node.leaf(pa.nb(pa.B(ds)))])

# the fit of one step (with any fuel above 0) is the view of T + 1
def pa.FT(+ds: List<&2, Bool>, +f: Nat) -> Type:
  {Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, OFit.fit.go(1n+f, OFit.choose(OFit.Last{}, pa.T2(ds), pa.bud(ds), 0n, OInfo.All{1n}, pa.V(ds)), OFit.Last{}, pa.T2(ds), pa.bud(ds), 0n, OInfo.All{1n}, pa.V(ds))) == pa.GV(pa.inc(ds)) : List<&2, ONode.Node>}
