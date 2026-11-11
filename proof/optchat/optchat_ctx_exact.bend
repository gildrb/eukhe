# eukhe: the proof of LAW optchat_ctx_exact
# The compaction's view keeps the compaction view's lines while each is
# built and ends by the bound, and stops at the first that is not
# (cx.go); the bound in bits is worth the spec's (LQ.oq.bound) and a
# line's end compares in bits as in numbers (LQ.oq.le).

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/ctx.bend as OCtx
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/state.bend as OState
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/queries.bend as LQ

def cx.keep(k: Bool, +info: OInfo.Info, +b: Nat, +h: ONode.Node, ek: {k == S.shown(info, b, h) : Bool}, -rec: List<&2, ONode.Node>, -t: List<&2, ONode.Node>, ih: S.CtxOf(info, b, rec, t)) -> S.CtxOf(info, b, OCtx.ctx.keep(k, h, rec), h <> t):
  match k:
    case True{}:
      ({==}, (Equal.sym(Bool, True{}, S.shown(info, b, h), ek), ih))
    case False{}:
      Equal.sym(Bool, False{}, S.shown(info, b, h), ek)

def cx.go(v: List<&2, ONode.Node>, +info: OInfo.Info, +bd: List<&2, Bool>) -> S.CtxOf(info, OBits.Bits.val(bd), OCtx.ctx.go(v, info, bd), v):
  match v:
    case Nil{}:
      Unit{}
    case +h <> +t:
      +b = OBits.Bits.val(bd)
      cx.keep(OCtx.ctx.ok(info, bd, h), info, b, h, Equal.cong(Bool, Bool, x => Bool.and(x, OInfo.Info.built(info, h)), OBits.Bits.le(OCtx.Node.end_bits(h), bd), Nat.is_le(S.line_end(h), b), LQ.oq.le(h, bd)), OCtx.ctx.go(t, info, bd), t, cx.go(t, info, bd))

def OptchatQueries.optchat_ctx_exact(s, n):
  %LQ.oq.bound(n) : S.CtxOf(OState.St.info(s), _, OCtx.ctx(s, n), OState.St.cview(s))
  cx.go(OState.St.cview(s), OState.St.info(s), OCtx.ctx.bound(n))
