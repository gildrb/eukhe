# spec: what the laws of LAWS.bend speak of, over the model in
# bend/optchat/. PROOF.bend and the proof modules beside this file use it
# too.

import Base
import ./optchat/bits.bend as OBits
import ./optchat/node.bend as ONode
import ./optchat/info.bend as OInfo
import ./optchat/fit.bend as OFit
import ./optchat/state.bend as OState
import ./optchat/step.bend as OStep
import ./optchat/ctx.bend as OCtx

# What the laws speak of
# ----------------------

# Tiles(s, v, e): the lines of v cover the messages s..e-1, each message
# once, contiguous, oldest first. A line is a tree node: node(l, i)
# covers the 2^l messages from i·2^l on.
def Tiles(s: Nat, v: List<&2, ONode.Node>, e: Nat) -> Type:
  match v:
    case Nil{}:
      {s == e : Nat}
    case +h <> t:
      ({ONode.Node.start(h) == s : Nat} & Tiles(Nat.add(s, ONode.Node.count(h)), t, e))

# Here(info, x, rest, z, w): x and the first line of rest are the two
# halves of a built parent z, and w is the rest after them
def Here(+info: OInfo.Info, +x: ONode.Node, rest: List<&2, ONode.Node>, +z: ONode.Node, +w: List<&2, ONode.Node>) -> Type:
  match rest:
    case Nil{}:
      Empty
    case +y <> more:
      ({OFit.mergeable(info, x, y) == True{} : Bool} & ({z == ONode.Node.parent(x) : ONode.Node} & {w == more : List<&2, ONode.Node>}))

# Merged(info, v, w): w is v with one pair of sibling lines replaced by
# their built parent, and nothing else changed
def Merged(+info: OInfo.Info, v: List<&2, ONode.Node>, w: List<&2, ONode.Node>) -> Type:
  match v w:
    case Nil{} _:
      Empty
    case +x <> vr Nil{}:
      Empty
    case +x <> +vr +z <> +wr:
      Or(Here(info, x, vr, z, wr), ({x == z : ONode.Node} & Merged(info, vr, wr)))

# some pair of adjacent lines may merge (its parent is built)
def can_merge(+info: OInfo.Info, v: List<&2, ONode.Node>) -> Bool:
  match v:
    case Nil{}:
      False{}
    case +x <> +rest:
      Bool.or(OFit.pair.ok(info, x, List.head(&2, ONode.Node, rest)), can_merge(info, rest))

# every node of v is built
def Built(+info: OInfo.Info, v: List<&2, ONode.Node>) -> Type:
  match v:
    case Nil{}:
      Unit
    case +h <> t:
      ({OInfo.Info.built(info, h) == True{} : Bool} & Built(info, t))

# every line of v that merges messages (level above 0) is built; a
# message's own line may wait for its summary
def Summarized(+info: OInfo.Info, v: List<&2, ONode.Node>) -> Type:
  match v:
    case Nil{}:
      Unit
    case +h <> t:
      ({OBits.Bool.implies(OBits.Nat.is_pos(ONode.Node.lvl(h)), OInfo.Info.built(info, h)) == True{} : Bool} & Summarized(info, t))

# every line of v ends by message b (in binary), and is built
def Before(+info: OInfo.Info, +b: List<&2, Bool>, v: List<&2, ONode.Node>) -> Type:
  match v:
    case Nil{}:
      Unit
    case +h <> t:
      ({OBits.Bits.le(OCtx.Node.end_bits(h), b) == True{} : Bool} & ({OInfo.Info.built(info, h) == True{} : Bool} & Before(info, b, t)))

# p is a prefix of v
def Prefix(p: List<&2, ONode.Node>, v: List<&2, ONode.Node>) -> Type:
  match p v:
    case Nil{} _:
      Unit
    case +x <> pr Nil{}:
      Empty
    case +x <> pr +y <> vr:
      ({x == y : ONode.Node} & Prefix(pr, vr))

# bs has no high zero bit (as Bits.inc and Bits.up make bits): its last
# bit, if any, is True
def Bits.canon.go(t: List<&2, Bool>, h: Bool) -> Bool:
  match t:
    case Nil{}:
      h
    case x <> r:
      Bits.canon.go(r, x)

def Bits.canon(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case h <> t:
      Bits.canon.go(t, h)

# every line of v has an index without a high zero bit
def Canon(v: List<&2, ONode.Node>) -> Bool:
  match v:
    case Nil{}:
      True{}
    case ONode.Node{l, i} <> rest:
      Bool.and(Bits.canon(i), Canon(rest))

def view.of(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> List<&2, ONode.Node>:
  OState.St.view(OStep.run(cfg, evs))

def cview.of(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> List<&2, ONode.Node>:
  OState.St.cview(OStep.run(cfg, evs))

def total.of(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> Nat:
  OBits.Bits.val(OState.St.t(OStep.run(cfg, evs)))

def ten() -> List<&2, Bool>:
  [False{}, True{}, False{}, True{}]

def view10() -> List<&2, ONode.Node>:
  [ONode.Node{2n, []}, ONode.Node{2n, [True{}]}, ONode.Node{0n, [False{}, False{}, False{}, True{}]}, ONode.Node{0n, [True{}, False{}, False{}, True{}]}]

