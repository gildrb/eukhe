# eukhe: the proof of LAW context_ends_at_node

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../LAWS.bend as Laws
import ../base.bend as L

def pf.ctx_bef.keep(k: Bool, +info: O.Info, +bound: List<&2, Bool>, +h: O.Node, -rec: List<&2, O.Node>, +e: {k == O.ctx.ok(info, bound, h) : Bool}, ih: S.Before(info, bound, rec))
  -> S.Before(info, bound, O.ctx.keep(k, h, rec)):
  match k:
    case False{}:
      Unit{}
    case True{}:
      (L.pf.and_l(O.Bits.le(O.Node.end_bits(h), bound), O.Info.built(info, h), Equal.sym(Bool, True{}, O.ctx.ok(info, bound, h), e)), (L.pf.and_r(O.Bits.le(O.Node.end_bits(h), bound), O.Info.built(info, h), Equal.sym(Bool, True{}, O.ctx.ok(info, bound, h), e)), ih))

def pf.ctx_bef(v: List<&2, O.Node>, +info: O.Info, +bound: List<&2, Bool>) -> S.Before(info, bound, O.ctx.go(v, info, bound)):
  match v:
    case Nil{}:
      Unit{}
    case +h <> +rest:
      pf.ctx_bef.keep(O.ctx.ok(info, bound, h), info, bound, h, O.ctx.go(rest, info, bound), {==}, pf.ctx_bef(rest, info, bound))

def context_ends_at_node(+s: O.St, +n: O.Node) -> S.Before(O.St.info(s), O.ctx.bound(n), O.ctx(s, n)):
  pf.ctx_bef(O.St.cview(s), O.St.info(s), O.ctx.bound(n))

# (g) A compaction's view

def Laws.context_ends_at_node(s, n):
  context_ends_at_node(s, n)
