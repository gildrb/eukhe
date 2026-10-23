# optchat: due keys and the merge sort: candidate pairs most due first, older on ties

import Base
import ./bits.bend as OBits
import ./node.bend as ONode
import ./ancestors.bend as OAncestors

# Keys. The pair from h = (l, i) is due (u - e)/2^l, with u = T + 1 and
# e = (i+2)·2^l its end: the whole number q = (u >> l) - i - 2 plus the
# fraction (u mod 2^l)/2^l, kept as f = (u mod 2^l)·2^(H - l) for the
# highest level H. Every number here is at most u.

# the value of bits (2x as x + x: native)
def fitx.val(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case h <> t:
      +v = fitx.val(t)
      OBits.bit(h, Nat.add(v, v))

# x·2^k
def fitx.shl(k: Nat, x: Nat) -> Nat:
  match k:
    case 0n:
      x
    case 1n+j:
      +y = x
      fitx.shl(j, Nat.add(y, y))

def fitx.take(k: Nat, bs: List<&2, Bool>) -> List<&2, Bool>:
  match k bs:
    case 0n _:
      Nil{}
    case 1n+j Nil{}:
      Nil{}
    case 1n+j h <> t:
      h <> fitx.take(j, t)

def fitx.drop(k: Nat, bs: List<&2, Bool>) -> List<&2, Bool>:
  match k bs:
    case 0n bs:
      bs
    case 1n+j Nil{}:
      Nil{}
    case 1n+j h <> t:
      fitx.drop(j, t)

type Due is Data:
  Due{q: Nat, f: Nat, s: Nat, p: OAncestors.Cand}

def Due.c(x: Due) -> OAncestors.Cand:
  match x:
    case Due{q, f, s, p}:
      p

def fitx.key(+u: List<&2, Bool>, +top: Nat, p: OAncestors.Cand) -> Due:
  match p:
    case OAncestors.Cand{h, z}:
      match h:
        case ONode.Node{+l, +i}:
          +iv = fitx.val(i)
          Due{Nat.sub(fitx.val(fitx.drop(l, u)), Nat.add(iv, 2n)), fitx.shl(Nat.sub(top, l), fitx.val(fitx.take(l, u))), fitx.shl(l, iv), OAncestors.Cand{ONode.Node{l, i}, z}}

def fitx.keys(ps: List<&2, OAncestors.Cand>, +u: List<&2, Bool>, +top: Nat) -> List<&2, Due>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      fitx.key(u, top, p) <> fitx.keys(rest, u, top)

def fitx.hi(ps: List<&2, OAncestors.Cand>, acc: Nat) -> Nat:
  match ps:
    case Nil{}:
      acc
    case OAncestors.Cand{h, z} <> rest:
      fitx.hi(rest, Nat.max(acc, ONode.Node.lvl(h)))

def fitx.tie2(c: Cmp, +sa: Nat, +sb: Nat) -> Bool:
  match c:
    case GT{}:
      True{}
    case LT{}:
      False{}
    case EQ{}:
      Nat.is_lt(sa, sb)

def fitx.tie(c: Cmp, +fa: Nat, +fb: Nat, +sa: Nat, +sb: Nat) -> Bool:
  match c:
    case GT{}:
      True{}
    case LT{}:
      False{}
    case EQ{}:
      fitx.tie2(Nat.cmp(fa, fb), sa, sb)

# a before b: more due, or as due and older
def fitx.before(+a: Due, +b: Due) -> Bool:
  match a b:
    case Due{+qa, +fa, +sa, pa} Due{+qb, +fb, +sb, pb}:
      fitx.tie(Nat.cmp(qa, qb), fa, fb, sa, sb)

# merge sort (the binary counter of the skill's sort example)
type KTree is Data:
  KTip{}
  KLeaf{n: Due}
  KNode{l: KTree, r: KTree}

type KDigits is Data:
  KEnd{}
  KZero{rest: KDigits}
  KOne{tree: KTree, rest: KDigits}

def kd.push(ds: KDigits, t: KTree) -> KDigits:
  match ds:
    case KEnd{}:
      KOne{t, KEnd{}}
    case KZero{rest}:
      KOne{t, rest}
    case KOne{t2, rest}:
      KZero{kd.push(rest, KNode{t2, t})}

def kd.build(xs: List<&2, Due>, ds: KDigits) -> KDigits:
  match xs:
    case Nil{}:
      ds
    case h <> t:
      kd.build(t, kd.push(ds, KLeaf{h}))

def kd.join(ds: KDigits, acc: KTree) -> KTree:
  match ds:
    case KEnd{}:
      acc
    case KZero{rest}:
      kd.join(rest, acc)
    case KOne{t, rest}:
      kd.join(rest, KNode{t, acc})

def kmerge.go(xt: List<&2, Due>, yt: List<&2, Due>, +x: Due, +y: Due, x_first: Bool) -> List<&2, Due>:
  match xt yt x_first:
    case Nil{} Nil{} True{}:
      x <> y <> Nil{}
    case Nil{} Nil{} False{}:
      y <> x <> Nil{}
    case Nil{} +y2 <> yt2 True{}:
      x <> y <> y2 <> yt2
    case Nil{} +y2 <> yt2 False{}:
      y <> kmerge.go(Nil{}, yt2, x, y2, fitx.before(x, y2))
    case +x2 <> xt2 Nil{} True{}:
      x <> kmerge.go(xt2, Nil{}, x2, y, fitx.before(x2, y))
    case +x2 <> xt2 Nil{} False{}:
      y <> x <> x2 <> xt2
    case +x2 <> xt2 +y2 <> yt2 True{}:
      x <> kmerge.go(xt2, y2 <> yt2, x2, y, fitx.before(x2, y))
    case +x2 <> xt2 +y2 <> yt2 False{}:
      y <> kmerge.go(x2 <> xt2, yt2, x, y2, fitx.before(x, y2))

def kmerge(xs: List<&2, Due>, ys: List<&2, Due>) -> List<&2, Due>:
  match xs ys:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} +y <> yt:
      y <> yt
    case +x <> xt Nil{}:
      x <> xt
    case +x <> xt +y <> yt:
      kmerge.go(xt, yt, x, y, fitx.before(x, y))

def ksort(tr: KTree) -> List<&2, Due>:
  match tr:
    case KTip{}:
      Nil{}
    case KLeaf{n}:
      [n]
    case KNode{l, r}:
      kmerge(ksort(l), ksort(r))

def fitx.pairs(ks: List<&2, Due>) -> List<&2, OAncestors.Cand>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> rest:
      Due.c(k) <> fitx.pairs(rest)

def fitx.sort(+t: List<&2, Bool>, +ps: List<&2, OAncestors.Cand>) -> List<&2, OAncestors.Cand>:
  fitx.pairs(ksort(kd.join(kd.build(fitx.keys(ps, OBits.Bits.inc(t), fitx.hi(ps, 0n)), KEnd{}), KTip{})))
