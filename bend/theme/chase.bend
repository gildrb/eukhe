# theme: resolving a value through a file's variables: the indexed variable trees and the cycle-checked walk

import Base
import ../color.bend as Co
import ./file.bend as TFile

# Variables
# ----------

# a value resolved: a color, or why it is none
type Got is Data:
  Hit{v: TFile.Val}
  Miss{why: TFile.Why}

# one step along a chain of variables, as the rule (LAWS.bend th.next)
# takes it: its end, or the next value to read with the variables met so
# far
type Step is Data:
  Stop{g: Got}
  Go{seen: List<&2, Nat>, j: TFile.Json}

# i is in xs (stops at the first hit)
def seen.has(xs: List<&2, Nat>, +i: Nat, hit: Bool) -> Bool:
  match xs:
    case Nil{}:
      hit
    case Con{x, rest}:
      match hit:
        case True{}:
          True{}
        case False{}:
          seen.has(rest, i, Nat.is_eq(x, i))

# the value of the variable at index n
def var.val(xs: List<&2, TFile.Var>, n: Nat) -> Maybe<&2, TFile.Json>:
  match xs n:
    case Nil{} _:
      None{}
    case Con{TFile.Var{nm, v}, rest} 0n:
      Some{v}
    case Con{x, rest} 1n+p:
      var.val(rest, p)

def hex.got(m: Maybe<&2, Co.Rgb>, s: String) -> Got:
  match m:
    case None{}:
      Miss{TFile.BadHex{s}}
    case Some{c}:
      Hit{TFile.Hex{c}}

def num.got(m: Maybe<&2, U32>, text: String) -> Got:
  match m:
    case None{}:
      Miss{TFile.BadValue{text}}
    case Some{i}:
      Hit{TFile.Idx{i}}

# The variables, indexed
# ----------------------
# The variables sit in a tree split by index (a node keeps the first h of
# its variables on its lo side), so a lookup costs a step per level, not
# a step per variable before it; the variables met so far sit in a tree of
# the same shape. Any split answers as the list does (only the speed
# depends on it): the build halves.

type VT is Data:
  VL{xs: List<&2, TFile.Var>}
  VN{h: Nat, lo: VT, hi: VT}

def vt.h(t: VT) -> Nat:
  match t:
    case VL{xs}:
      0n
    case VN{h, lo, hi}:
      h

# the value of variable i, lt telling whether i is below t's split
def vt.get(t: VT, lt: Bool, +i: Nat) -> Maybe<&2, TFile.Json>:
  match t:
    case VL{xs}:
      var.val(xs, i)
    case VN{+h, +lo, +hi}:
      match lt:
        case True{}:
          vt.get(lo, Nat.is_lt(i, vt.h(lo)), i)
        case False{}:
          +k = Nat.sub(i, h)
          vt.get(hi, Nat.is_lt(k, vt.h(hi)), k)

# the value of variable i
def vt.at(+t: VT, +i: Nat) -> Maybe<&2, TFile.Json>:
  vt.get(t, Nat.is_lt(i, vt.h(t)), i)

# the n variables xs as a tree; small: n is at most 1; fuel bounds the
# depth
def vt.build(fuel: Nat, small: Bool, +xs: List<&2, TFile.Var>, +n: Nat) -> VT:
  match fuel:
    case 0n:
      VL{xs}
    case 1n++f:
      match small:
        case True{}:
          VL{xs}
        case False{}:
          +h = Nat.div(n, 2n)
          +r = Nat.sub(n, h)
          VN{h, vt.build(f, Nat.is_le(h, 1n), List.take(&2, TFile.Var, xs, h), h), vt.build(f, Nat.is_le(r, 1n), List.drop(&2, TFile.Var, xs, h), r)}

type ST is Data:
  SL{xs: List<&2, Nat>}
  SN{h: Nat, lo: ST, hi: ST}

def st.h(t: ST) -> Nat:
  match t:
    case SL{xs}:
      0n
    case SN{h, lo, hi}:
      h

# no variable met, in a tree of t's shape
def st.of(t: VT) -> ST:
  match t:
    case VL{xs}:
      SL{Nil{}}
    case VN{h, lo, hi}:
      SN{h, st.of(lo), st.of(hi)}

# variable i was met, lt telling whether i is below t's split
def st.has(t: ST, lt: Bool, +i: Nat) -> Bool:
  match t:
    case SL{xs}:
      seen.has(xs, i, False{})
    case SN{+h, +lo, +hi}:
      match lt:
        case True{}:
          st.has(lo, Nat.is_lt(i, st.h(lo)), i)
        case False{}:
          +k = Nat.sub(i, h)
          st.has(hi, Nat.is_lt(k, st.h(hi)), k)

def st.mem(+t: ST, +i: Nat) -> Bool:
  st.has(t, Nat.is_lt(i, st.h(t)), i)

# variable i met too, lt telling whether i is below t's split
def st.ins(t: ST, lt: Bool, +i: Nat) -> ST:
  match t:
    case SL{xs}:
      SL{i <> xs}
    case SN{+h, +lo, +hi}:
      match lt:
        case True{}:
          SN{h, st.ins(lo, Nat.is_lt(i, st.h(lo)), i), hi}
        case False{}:
          +k = Nat.sub(i, h)
          SN{h, lo, st.ins(hi, Nat.is_lt(k, st.h(hi)), k)}

def st.add(+t: ST, +i: Nat) -> ST:
  st.ins(t, Nat.is_lt(i, st.h(t)), i)

# one step along a chain of variables over the trees: its end, or the
# next value to read with the variables met so far
type FStep is Data:
  FStop{g: Got}
  FGo{seen: ST, j: TFile.Json}

def look.next(m: Maybe<&2, TFile.Json>, seen: ST, s: String) -> FStep:
  match m:
    case None{}:
      FStop{Miss{TFile.NotFound{s}}}
    case Some{j}:
      FGo{seen, j}

def look.var(looped: Bool, +vt: VT, +seen: ST, s: String, +i: Nat) -> FStep:
  match looped:
    case True{}:
      FStop{Miss{TFile.Circular{s}}}
    case False{}:
      look.next(vt.at(vt, i), st.add(seen, i), s)

def look.ref(+vt: VT, +seen: ST, s: String, at: Maybe<&2, Nat>) -> FStep:
  match at:
    case None{}:
      FStop{Miss{TFile.NotFound{s}}}
    case Some{+i}:
      look.var(st.mem(seen, i), vt, seen, s, i)

def look.sym(sharp: Bool, +vt: VT, +seen: ST, +s: String, at: Maybe<&2, Nat>) -> FStep:
  match sharp:
    case True{}:
      FStop{hex.got(Co.hex(s), s)}
    case False{}:
      look.ref(vt, seen, s, at)

def look.str(+vt: VT, +seen: ST, s: String, at: Maybe<&2, Nat>) -> FStep:
  match s:
    case SNil{}:
      FStop{Hit{TFile.Dflt{}}}
    case SCon{+c, rest}:
      look.sym(Char.is_eq(c, '#'), vt, seen, SCon{c, rest}, at)

# read one value: "" is the terminal default, a #-string a hex color, any
# other string names a variable (met before: a cycle); a number is an
# index; anything else is no color
def look.step(+vt: VT, +seen: ST, j: TFile.Json) -> FStep:
  match j:
    case TFile.JStr{s, at}:
      look.str(vt, seen, s, at)
    case TFile.JNum{+text}:
      FStop{num.got(Co.num(text), text)}
    case TFile.JOther{text}:
      FStop{Miss{TFile.BadValue{text}}}

# follow the steps for at most fuel of them
def look.walk(fuel: Nat, +vt: VT, fs: FStep) -> Got:
  match fuel:
    case 0n:
      match fs:
        case FStop{g}:
          g
        case FGo{seen, j}:
          Miss{TFile.Circular{""}}
    case 1n+f:
      match fs:
        case FStop{g}:
          g
        case FGo{seen, j}:
          look.walk(f, vt, look.step(vt, seen, j))

# a file's variables, indexed: their tree, the empty seen tree of its
# shape, and the steps a chase may take (one more than there are
# variables: each step past the first meets a new variable)
type Ix is Data:
  Ix{vt: VT, seen: ST, fuel: Nat}

def index.of(+vt: VT, n: Nat) -> Ix:
  Ix{vt, st.of(vt), 1n+n}

def index(+vars: List<&2, TFile.Var>) -> Ix:
  +n = List.length(&2, TFile.Var, vars)
  index.of(vt.build(n, Nat.is_le(n, 1n), vars, n), n)

# the color a value resolves to through the indexed variables
def look(ix: Ix, j: TFile.Json) -> Got:
  match ix:
    case Ix{vt, seen, fuel}:
      look.walk(fuel, vt, FGo{seen, j})

# the color a value resolves to through the variables
def chase(+vars: List<&2, TFile.Var>, j: TFile.Json) -> Got:
  look(index(vars), j)
