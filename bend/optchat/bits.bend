# optchat: numbers and binary naturals (lowest bit first): pow2/shl, bit arithmetic, comparison, boolean helpers
#
# optchat: the pure core of eukhe's chat memory, after Victor Taelin's
# OptChat gist (maps every rule of it to this file, to the
# Rust code and to LAWS.bend).
#
# - A node(l, i) covers the 2^l messages from i·2^l on (gist §2). Its
#   index i is kept in binary, lowest bit first, so its parent is one
#   step away: node(l+1, i/2) drops the lowest bit.
# - The view is an ordered list of nodes (gist §3). Each message appends
#   its line; once the view passes the ceiling, one batch merges the most
#   due pairs, due = (T - last) / 2^l, oldest first on ties, until it is
#   at most the floor (gist §3.2).
# - The compaction view is the view merged further, with its own
#   sawtooth; a compaction sees it up to its node (gist §4).
# - The work queue starts nodes in the gist's order (gist §4).
#
# LAWS.bend states what must hold; PROOF.bend proves it. bridge/bridge.bend
# runs this model on the scenarios the Rust bridge test sends.

import Base

# Numbers
# -------

# 2^l
def pow2(l: Nat) -> Nat:
  match l:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

# x·2^l
def shl(l: Nat, x: Nat) -> Nat:
  match l:
    case 0n:
      x
    case 1n+p:
      shl(p, Nat.double(x))

# Bits
# ----
# A number in binary, lowest bit first, without high zero bits: 0 is [],
# 6 is [False, True, True].

def bit(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      x
    case True{}:
      1n+x

def Bits.val(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case h <> t:
      bit(h, Nat.double(Bits.val(t)))

def Bits.inc(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      [True{}]
    case h <> t:
      match h:
        case False{}:
          True{} <> t
        case True{}:
          False{} <> Bits.inc(t)

# the lowest bit (0 for 0)
def Bits.low(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case h <> t:
      h

# the number halved (the bits above the lowest)
def Bits.up(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

def Bool.eq(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      Bool.not(b)
    case True{}:
      b

def Bits.eq(as: List<&2, Bool>, bs: List<&2, Bool>) -> Bool:
  match as bs:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> ys:
      False{}
    case x <> xs Nil{}:
      False{}
    case x <> xs y <> ys:
      Bool.and(Bool.eq(x, y), Bits.eq(xs, ys))

# The planner's arithmetic runs on bits, so the kernel checks long runs
# fast; high zero bits are tolerated.

# x·2^l: l zero bits below x
def Bits.shl(l: Nat, x: List<&2, Bool>) -> List<&2, Bool>:
  match l:
    case 0n:
      x
    case 1n+p:
      False{} <> Bits.shl(p, x)

# x + 1 when c holds
def Bits.inc_if(c: Bool, x: List<&2, Bool>) -> List<&2, Bool>:
  match c:
    case False{}:
      x
    case True{}:
      Bits.inc(x)

# x + y + c
def Bits.add.go(xs: List<&2, Bool>, ys: List<&2, Bool>, +c: Bool) -> List<&2, Bool>:
  match xs ys:
    case Nil{} _:
      Bits.inc_if(c, ys)
    case x <> xt Nil{}:
      Bits.inc_if(c, x <> xt)
    case +x <> xt +y <> yt:
      Bool.xor(Bool.xor(x, y), c) <> Bits.add.go(xt, yt, Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))))

def Bits.add(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  Bits.add.go(xs, ys, False{})

def Bits.is_zero(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(Bool.not(h), Bits.is_zero(t))

# the higher bits decide, unless equal
def Cmp.then(hi: Cmp, lo: Cmp) -> Cmp:
  match hi:
    case EQ{}:
      lo
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def Cmp.of_zero(z: Bool, ne: Cmp) -> Cmp:
  match z:
    case True{}:
      EQ{}
    case False{}:
      ne

def Bits.cmp(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Cmp:
  match xs ys:
    case Nil{} _:
      Cmp.of_zero(Bits.is_zero(ys), LT{})
    case x <> xt Nil{}:
      Cmp.of_zero(Bits.is_zero(x <> xt), GT{})
    case x <> xt y <> yt:
      Cmp.then(Bits.cmp(xt, yt), Bool.cmp(x, y))

def Bits.gt(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  Cmp.is_gt(Bits.cmp(xs, ys))

def Bits.le(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  Cmp.is_le(Bits.cmp(xs, ys))

def Bits.same(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  Cmp.is_eq(Bits.cmp(xs, ys))

def Bool.implies(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      True{}
    case True{}:
      b

def Nat.is_pos(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}
