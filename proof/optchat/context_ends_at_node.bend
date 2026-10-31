# eukhe: the proof of LAW context_ends_at_node

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/ctx.bend as OCtx
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/state.bend as OState
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat.bend as Optchat
import ../base/logic/bool.bend as LLogicBool

def pf.ctx_bef.keep(k: Bool, +info: OInfo.Info, +bound: List<&2, Bool>, +h: ONode.Node, -rec: List<&2, ONode.Node>, +e: {k == OCtx.ctx.ok(info, bound, h) : Bool}, ih: S.Before(info, bound, rec))
  -> S.Before(info, bound, OCtx.ctx.keep(k, h, rec)):
  match k:
    case False{}:
      Unit{}
    case True{}:
      (LLogicBool.pf.and_l(OBits.Bits.le(OCtx.Node.end_bits(h), bound), OInfo.Info.built(info, h), Equal.sym(Bool, True{}, OCtx.ctx.ok(info, bound, h), e)), (LLogicBool.pf.and_r(OBits.Bits.le(OCtx.Node.end_bits(h), bound), OInfo.Info.built(info, h), Equal.sym(Bool, True{}, OCtx.ctx.ok(info, bound, h), e)), ih))

def pf.ctx_bef(v: List<&2, ONode.Node>, +info: OInfo.Info, +bound: List<&2, Bool>) -> S.Before(info, bound, OCtx.ctx.go(v, info, bound)):
  match v:
    case Nil{}:
      Unit{}
    case +h <> +rest:
      pf.ctx_bef.keep(OCtx.ctx.ok(info, bound, h), info, bound, h, OCtx.ctx.go(rest, info, bound), {==}, pf.ctx_bef(rest, info, bound))

def context_ends_at_node(+s: OState.St, +n: ONode.Node) -> S.Before(OState.St.info(s), OCtx.ctx.bound(n), OCtx.ctx(s, n)):
  pf.ctx_bef(OState.St.cview(s), OState.St.info(s), OCtx.ctx.bound(n))

# (g) A compaction's view

def Optchat.context_ends_at_node(s, n):
  context_ends_at_node(s, n)
