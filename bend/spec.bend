# spec: what the laws of LAWS.bend speak of, over the model in
# optchat.bend. PROOF.bend and the proof modules beside this file use it
# too.

import Base
import ./optchat.bend as O

# What the laws speak of
# ----------------------

# Tiles(s, v, e): the lines of v cover the messages s..e-1, each message
# once, contiguous, oldest first. A line is a tree node: node(l, i)
# covers the 2^l messages from i·2^l on.
def Tiles(s: Nat, v: List<&2, O.Node>, e: Nat) -> Type:
  match v:
    case Nil{}:
      {s == e : Nat}
    case +h <> t:
      ({O.Node.start(h) == s : Nat} & Tiles(Nat.add(s, O.Node.count(h)), t, e))

# Here(info, x, rest, z, w): x and the first line of rest are the two
# halves of a built parent z, and w is the rest after them
def Here(+info: O.Info, +x: O.Node, rest: List<&2, O.Node>, +z: O.Node, +w: List<&2, O.Node>) -> Type:
  match rest:
    case Nil{}:
      Empty
    case +y <> more:
      ({O.mergeable(info, x, y) == True{} : Bool} & ({z == O.Node.parent(x) : O.Node} & {w == more : List<&2, O.Node>}))

# Merged(info, v, w): w is v with one pair of sibling lines replaced by
# their built parent, and nothing else changed
def Merged(+info: O.Info, v: List<&2, O.Node>, w: List<&2, O.Node>) -> Type:
  match v w:
    case Nil{} _:
      Empty
    case +x <> vr Nil{}:
      Empty
    case +x <> +vr +z <> +wr:
      Or(Here(info, x, vr, z, wr), ({x == z : O.Node} & Merged(info, vr, wr)))

# some pair of adjacent lines may merge (its parent is built)
def can_merge(+info: O.Info, v: List<&2, O.Node>) -> Bool:
  match v:
    case Nil{}:
      False{}
    case +x <> +rest:
      Bool.or(O.pair.ok(info, x, List.head(&2, O.Node, rest)), can_merge(info, rest))

# every node of v is built
def Built(+info: O.Info, v: List<&2, O.Node>) -> Type:
  match v:
    case Nil{}:
      Unit
    case +h <> t:
      ({O.Info.built(info, h) == True{} : Bool} & Built(info, t))

# every line of v that merges messages (level above 0) is built; a
# message's own line may wait for its summary
def Summarized(+info: O.Info, v: List<&2, O.Node>) -> Type:
  match v:
    case Nil{}:
      Unit
    case +h <> t:
      ({O.Bool.implies(O.Nat.is_pos(O.Node.lvl(h)), O.Info.built(info, h)) == True{} : Bool} & Summarized(info, t))

# every line of v ends by message b (in binary), and is built
def Before(+info: O.Info, +b: List<&2, Bool>, v: List<&2, O.Node>) -> Type:
  match v:
    case Nil{}:
      Unit
    case +h <> t:
      ({O.Bits.le(O.Node.end_bits(h), b) == True{} : Bool} & ({O.Info.built(info, h) == True{} : Bool} & Before(info, b, t)))

# p is a prefix of v
def Prefix(p: List<&2, O.Node>, v: List<&2, O.Node>) -> Type:
  match p v:
    case Nil{} _:
      Unit
    case +x <> pr Nil{}:
      Empty
    case +x <> pr +y <> vr:
      ({x == y : O.Node} & Prefix(pr, vr))

def view.of(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> List<&2, O.Node>:
  O.St.view(O.run(cfg, evs))

def cview.of(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> List<&2, O.Node>:
  O.St.cview(O.run(cfg, evs))

def total.of(+cfg: O.Cfg, +evs: List<&2, O.Ev>) -> Nat:
  O.Bits.val(O.St.t(O.run(cfg, evs)))

def ten() -> List<&2, Bool>:
  [False{}, True{}, False{}, True{}]

def view10() -> List<&2, O.Node>:
  [O.Node{2n, []}, O.Node{2n, [True{}]}, O.Node{0n, [False{}, False{}, False{}, True{}]}, O.Node{0n, [True{}, False{}, False{}, True{}]}]

