# eukhe: the proof of LAW context_is_prefix

import Base
import ../../bend/optchat/ctx.bend as OCtx
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/state.bend as OState
import ../../bend/spec.bend as S
import ../../laws/optchat.bend as Optchat

# A compaction's view
# -------------------

def pf.ctx_pre.keep(k: Bool, +h: ONode.Node, -rec: List<&2, ONode.Node>, -rest: List<&2, ONode.Node>, ih: S.Prefix(rec, rest)) -> S.Prefix(OCtx.ctx.keep(k, h, rec), h <> rest):
  match k:
    case False{}:
      Unit{}
    case True{}:
      ({==}, ih)

def pf.ctx_pre(v: List<&2, ONode.Node>, +info: OInfo.Info, +bound: List<&2, Bool>) -> S.Prefix(OCtx.ctx.go(v, info, bound), v):
  match v:
    case Nil{}:
      Unit{}
    case +h <> +rest:
      pf.ctx_pre.keep(OCtx.ctx.ok(info, bound, h), h, OCtx.ctx.go(rest, info, bound), rest, pf.ctx_pre(rest, info, bound))

def context_is_prefix(+s: OState.St, +n: ONode.Node) -> S.Prefix(OCtx.ctx(s, n), OState.St.cview(s)):
  pf.ctx_pre(OState.St.cview(s), OState.St.info(s), OCtx.ctx.bound(n))

def Optchat.context_is_prefix(s, n):
  context_is_prefix(s, n)
