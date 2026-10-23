# optchat: a compaction's view: the compaction view up to its node

import Base
import ./bits.bend as OBits
import ./node.bend as ONode
import ./info.bend as OInfo
import ./state.bend as OState

# A compaction's view
# -------------------
# The compaction view up to the node: the lines before the message, or
# for a merge the lines up to its last message; it stops at the first
# unbuilt line (gist §4).

def Node.end_bits(n: ONode.Node) -> List<&2, Bool>:
  match n:
    case ONode.Node{l, i}:
      OBits.Bits.shl(l, OBits.Bits.inc(i))

def ctx.bound(n: ONode.Node) -> List<&2, Bool>:
  match n:
    case ONode.Node{l, i}:
      match l:
        case 0n:
          i
        case 1n+p:
          OBits.Bits.shl(1n+p, OBits.Bits.inc(i))

def ctx.keep(k: Bool, +h: ONode.Node, rec: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match k:
    case False{}:
      Nil{}
    case True{}:
      h <> rec

# a line stays when it ends by the bound and is built
def ctx.ok(+info: OInfo.Info, +bound: List<&2, Bool>, +h: ONode.Node) -> Bool:
  Bool.and(OBits.Bits.le(Node.end_bits(h), bound), OInfo.Info.built(info, h))

def ctx.go(v: List<&2, ONode.Node>, +info: OInfo.Info, +bound: List<&2, Bool>) -> List<&2, ONode.Node>:
  match v:
    case Nil{}:
      Nil{}
    case +h <> rest:
      ctx.keep(ctx.ok(info, bound, h), h, ctx.go(rest, info, bound))

# the view a compaction of node n sees
def ctx(+s: OState.St, +n: ONode.Node) -> List<&2, ONode.Node>:
  ctx.go(OState.St.cview(s), OState.St.info(s), ctx.bound(n))
