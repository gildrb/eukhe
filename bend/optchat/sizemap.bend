# optchat: the fast batch's node-to-size map (Mt tries per level)

import Base
import ./node.bend as ONode

# The fast batch
# --------------
# fit with the Last measure, fast (not run: bend/optchat/stepx.bend). Meant
# to be fit itself on a view that tiles the messages (a fitx_is_fit law is
# not stated yet). A merge always makes its parent's pair less
# due than the pair it merged, so no pair can become mergeable after a less
# due one: the batch takes, in one sort, every pair that could ever merge
# (each line's built ancestors), most due first (of equal ones the older),
# and merges each in turn whose two halves are lines then, while the view
# is over budget. O(L log L) instead of O(L) per merge.
#
# A map from nodes to sizes: per level (lowest first), a trie on the index
# bits. Used linearly (never shared).
type Mt is Data:
  MtTip{}
  MtBin{v: Maybe<&2, Nat>, lo: Mt, hi: Mt}

type Sizes is Data:
  SzEnd{}
  SzLv{t: Mt, rest: Sizes}

def mt.get(k: List<&2, Bool>, t: Mt) -> Maybe<&2, Nat>:
  match k t:
    case _ MtTip{}:
      None{}
    case Nil{} MtBin{v, lo, hi}:
      v
    case False{} <> r MtBin{v, lo, hi}:
      mt.get(r, lo)
    case True{} <> r MtBin{v, lo, hi}:
      mt.get(r, hi)

def mt.put(k: List<&2, Bool>, t: Mt, +z: Nat) -> Mt:
  match k t:
    case Nil{} MtTip{}:
      MtBin{Some{z}, MtTip{}, MtTip{}}
    case Nil{} MtBin{v, lo, hi}:
      MtBin{Some{z}, lo, hi}
    case False{} <> r MtTip{}:
      MtBin{None{}, mt.put(r, MtTip{}, z), MtTip{}}
    case True{} <> r MtTip{}:
      MtBin{None{}, MtTip{}, mt.put(r, MtTip{}, z)}
    case False{} <> r MtBin{v, lo, hi}:
      MtBin{v, mt.put(r, lo, z), hi}
    case True{} <> r MtBin{v, lo, hi}:
      MtBin{v, lo, mt.put(r, hi, z)}

def sizes.get(l: Nat, k: List<&2, Bool>, s: Sizes) -> Maybe<&2, Nat>:
  match l s:
    case _ SzEnd{}:
      None{}
    case 0n SzLv{t, rest}:
      mt.get(k, t)
    case 1n+p SzLv{t, rest}:
      sizes.get(p, k, rest)

def sizes.put(l: Nat, k: List<&2, Bool>, s: Sizes, +z: Nat) -> Sizes:
  match l s:
    case 0n SzEnd{}:
      SzLv{mt.put(k, MtTip{}, z), SzEnd{}}
    case 0n SzLv{t, rest}:
      SzLv{mt.put(k, t, z), rest}
    case 1n+p SzEnd{}:
      SzLv{MtTip{}, sizes.put(p, k, SzEnd{}, z)}
    case 1n+p SzLv{t, rest}:
      SzLv{t, sizes.put(p, k, rest, z)}

def fitx.get(+s: Sizes, n: ONode.Node) -> Maybe<&2, Nat>:
  match n:
    case ONode.Node{l, i}:
      sizes.get(l, i, s)

def fitx.put(s: Sizes, n: ONode.Node, +z: Nat) -> Sizes:
  match n:
    case ONode.Node{l, i}:
      sizes.put(l, i, s, z)

def fitx.has(+s: Sizes, n: ONode.Node) -> Bool:
  Maybe.is_some(&2, Nat, fitx.get(s, n))
