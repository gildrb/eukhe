# eukhe: the proof of LAW context_is_prefix

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../laws/optchat.bend as Optchat

# A compaction's view
# -------------------

def pf.ctx_pre.keep(k: Bool, +h: O.Node, -rec: List<&2, O.Node>, -rest: List<&2, O.Node>, ih: S.Prefix(rec, rest)) -> S.Prefix(O.ctx.keep(k, h, rec), h <> rest):
  match k:
    case False{}:
      Unit{}
    case True{}:
      ({==}, ih)

def pf.ctx_pre(v: List<&2, O.Node>, +info: O.Info, +bound: List<&2, Bool>) -> S.Prefix(O.ctx.go(v, info, bound), v):
  match v:
    case Nil{}:
      Unit{}
    case +h <> +rest:
      pf.ctx_pre.keep(O.ctx.ok(info, bound, h), h, O.ctx.go(rest, info, bound), rest, pf.ctx_pre(rest, info, bound))

def context_is_prefix(+s: O.St, +n: O.Node) -> S.Prefix(O.ctx(s, n), O.St.cview(s)):
  pf.ctx_pre(O.St.cview(s), O.St.info(s), O.ctx.bound(n))

def Optchat.context_is_prefix(s, n):
  context_is_prefix(s, n)
