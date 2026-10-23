# optchat: the built nodes: per-level tries of node sizes (Trie, Info)

import Base
import ./node.bend as ONode

# Built nodes
# -----------
# The size of every built node: one trie per level, keyed by the bits of
# the node's index. All{s} has every node built, each s bytes (for the
# comparison with push, where a line counts 1).

type Trie is Data:
  Tip{}
  Bin{val: Maybe<&2, Nat>, lo: Trie, hi: Trie}

def Trie.get(k: List<&2, Bool>, t: Trie) -> Maybe<&2, Nat>:
  match k t:
    case _ Tip{}:
      None{}
    case Nil{} Bin{v, lo, hi}:
      v
    case False{} <> r Bin{v, lo, hi}:
      Trie.get(r, lo)
    case True{} <> r Bin{v, lo, hi}:
      Trie.get(r, hi)

def Trie.set(k: List<&2, Bool>, t: Trie, +s: Nat) -> Trie:
  match k t:
    case Nil{} Tip{}:
      Bin{Some{s}, Tip{}, Tip{}}
    case Nil{} Bin{v, lo, hi}:
      Bin{Some{s}, lo, hi}
    case False{} <> r Tip{}:
      Bin{None{}, Trie.set(r, Tip{}, s), Tip{}}
    case True{} <> r Tip{}:
      Bin{None{}, Tip{}, Trie.set(r, Tip{}, s)}
    case False{} <> r Bin{v, lo, hi}:
      Bin{v, Trie.set(r, lo, s), hi}
    case True{} <> r Bin{v, lo, hi}:
      Bin{v, lo, Trie.set(r, hi, s)}

type Info is Data:
  All{size: Nat}
  Lvls{ts: List<&2, Trie>}

def Lvls.get(l: Nat, ts: List<&2, Trie>, k: List<&2, Bool>) -> Maybe<&2, Nat>:
  match l ts:
    case _ Nil{}:
      None{}
    case 0n h <> t:
      Trie.get(k, h)
    case 1n+p h <> t:
      Lvls.get(p, t, k)

def Lvls.set(l: Nat, ts: List<&2, Trie>, k: List<&2, Bool>, +s: Nat) -> List<&2, Trie>:
  match l ts:
    case 0n Nil{}:
      [Trie.set(k, Tip{}, s)]
    case 0n h <> t:
      Trie.set(k, h, s) <> t
    case 1n+p Nil{}:
      Tip{} <> Lvls.set(p, Nil{}, k, s)
    case 1n+p h <> t:
      h <> Lvls.set(p, t, k, s)

def Info.empty() -> Info:
  Lvls{Nil{}}

# the node's size, when it is built
def Info.get(info: Info, n: ONode.Node) -> Maybe<&2, Nat>:
  match info:
    case All{s}:
      Some{s}
    case Lvls{ts}:
      match n:
        case ONode.Node{l, i}:
          Lvls.get(l, ts, i)

# node n is built, s bytes
def Info.set(info: Info, n: ONode.Node, +s: Nat) -> Info:
  match info:
    case All{a}:
      All{a}
    case Lvls{ts}:
      match n:
        case ONode.Node{l, i}:
          Lvls{Lvls.set(l, ts, i, s)}

def Info.built(info: Info, n: ONode.Node) -> Bool:
  Maybe.is_some(&2, Nat, Info.get(info, n))
