# optchat: the fast batch fitx (not run: bend/optchat/stepx.bend): line sizes, the merge pass, the laid-out view

import Base
import ./bits.bend as OBits
import ./node.bend as ONode
import ./info.bend as OInfo
import ./fit.bend as OFit
import ./sizemap.bend as OSizemap
import ./ancestors.bend as OAncestors
import ./order.bend as OOrder

# The lines: their sizes (a map) and the view's size, in one pass.
def fitx.lines(v: List<&2, ONode.Node>, +ph: Nat, +info: OInfo.Info, s: OSizemap.Sizes, z: Nat) -> OSizemap.Sizes & Nat:
  match v:
    case Nil{}:
      (s, z)
    case +x <> rest:
      +sz = OFit.line_size(ph, info, x)
      fitx.lines(rest, ph, info, OSizemap.fitx.put(s, x, sz), Nat.add(z, sz))

# The pass: in that order, merge each pair whose two halves are lines now,
# while the view is over budget. lines: the line sizes (merged parents
# included), size: the view's bytes, acc: the merged parents, newest first.
type Pass is Data:
  Pass{lines: OSizemap.Sizes, size: Nat, acc: List<&2, ONode.Node>}

def fitx.hit(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, +h: ONode.Node, +z: Nat, s: Pass) -> Pass:
  match a b:
    case Some{x} Some{y}:
      match s:
        case Pass{lines, size, acc}:
          +p = ONode.Node.parent(h)
          Pass{OSizemap.fitx.put(lines, p, z), Nat.add(Nat.sub(size, Nat.add(x, y)), z), p <> acc}
    case _ _:
      s

def fitstepx(p: OAncestors.Cand, s: Pass) -> Pass:
  match p s:
    case OAncestors.Cand{+h, +z} Pass{+lines, size, acc}:
      fitx.hit(OSizemap.fitx.get(lines, h), OSizemap.fitx.get(lines, OAncestors.fitx.second(h)), h, z, Pass{lines, size, acc})

def fitx.size(s: Pass) -> Nat:
  match s:
    case Pass{l, z, a}:
      z

def fitx.pass(ps: List<&2, OAncestors.Cand>, over: Bool, +budget: Nat, s: Pass) -> Pass:
  match ps over:
    case Nil{} _:
      s
    case h <> rest False{}:
      s
    case h <> rest True{}:
      +s2 = fitstepx(h, s)
      fitx.pass(rest, Nat.is_gt(fitx.size(s2), budget), budget, s2)

# The view after the merges: a line stays unless merged; a merged parent
# takes the place of its first line.
def fitx.low(x: ONode.Node) -> Bool:
  match x:
    case ONode.Node{l, i}:
      OBits.Bits.low(i)

def fitx.top(fuel: Nat, up: Bool, +mg: OSizemap.Sizes, +x: ONode.Node, left: Bool) -> Maybe<&2, ONode.Node>:
  match fuel up:
    case 0n _:
      Some{x}
    case 1n+f False{}:
      match left:
        case True{}:
          Some{x}
        case False{}:
          None{}
    case 1n+f True{}:
      +p = ONode.Node.parent(x)
      fitx.top(f, OSizemap.fitx.has(mg, ONode.Node.parent(p)), mg, p, Bool.and(left, Bool.not(fitx.low(x))))

def fitx.lay.put(m: Maybe<&2, ONode.Node>, rest: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match m:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def fitx.lay(v: List<&2, ONode.Node>, +fuel: Nat, +mg: OSizemap.Sizes) -> List<&2, ONode.Node>:
  match v:
    case Nil{}:
      Nil{}
    case +x <> rest:
      fitx.lay.put(fitx.top(fuel, OSizemap.fitx.has(mg, ONode.Node.parent(x)), mg, x, True{}), fitx.lay(rest, fuel, mg))

def fitx.done(+fuel: Nat, v: List<&2, ONode.Node>, s: Pass) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  match s:
    case Pass{lines, size, acc}:
      (List.reverse(&2, ONode.Node, acc), fitx.lay(v, fuel, lines))

# the fuel of a walk up the tree: a node of a tiling of T messages has a
# level below the bits of T
def fitx.run(+t: List<&2, Bool>, +budget: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, lines: OSizemap.Sizes, +size: Nat) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  +fuel = List.length(&2, Bool, t)
  +ps = OOrder.fitx.sort(t, Pair.fst(List<&2, OAncestors.Cand>, OSizemap.Sizes, OAncestors.fitx.all(v, fuel, info, (Nil{}, OSizemap.SzEnd{}))))
  fitx.done(fuel, v, fitx.pass(ps, True{}, budget, Pass{lines, size, Nil{}}))

def fitx.if(over: Bool, +t: List<&2, Bool>, +budget: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, lines: OSizemap.Sizes, +size: Nat) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  match over:
    case False{}:
      (Nil{}, v)
    case True{}:
      fitx.run(t, budget, info, v, lines, size)

def fitx.go(+t: List<&2, Bool>, +budget: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, r: OSizemap.Sizes & Nat) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  (lines, size) = r
  +z = size
  fitx.if(Nat.is_gt(z, budget), t, budget, info, v, lines, z)

# = fit(Last{}, t, budget, ph, info, v) on a view that tiles 0..T
def fitx(+t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  fitx.go(t, budget, info, v, fitx.lines(v, ph, info, OSizemap.SzEnd{}, 0n))

# the view after fitx
def fitx.view(+t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, fitx(t, budget, ph, info, v))
