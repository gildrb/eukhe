# eukhe: the proof of LAW core_infer_ffi_exact
# The entry's decoder reads every input as the laws' reader does, stage by
# stage (ie.*, the tool list through ../director/list_ext.bend). The
# model's rank (a merge sort over a binary counter of trees) is the laws'
# stable insertion sort: the counter keeps the tools in order (pin.lv,
# pin.dl), the merge is a stable merge (pi2.*), and merging two sorted
# lists is sorting their concatenation (pin.n, pin.msort). The plan is
# then the laws' plan, spelled alike.

import Base
import ../../bend/infer.bend as If
import ../../bend/ffi_infer.bend as FIn
import ../../bend/wire.bend as Wr
import ../../laws/infer.bend as Infer
import ../base/nat.bend as LNat
import ../base/logic/logic.bend as LLogic
import ../director/list_ext.bend as LX

# Reading
# -------

def ie.mnat_some(r: Wr.Dec<Nat>) -> {FIn.get_mnat.some(r) == Infer.ir.mnat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ie.mnat_tag(t: Nat, +s: String) -> {FIn.get_mnat.tag(t, s) == Infer.ir.mnat.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      ie.mnat_some(Wr.get_nat(s))
    case 2n+p:
      {==}

def ie.mnat_go(r: Wr.Dec<Nat>) -> {FIn.get_mnat.go(r) == Infer.ir.mnat(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, +s}:
      ie.mnat_tag(t, s)
    case Wr.Bad{}:
      {==}

def ie.tool2(+i: Nat, d: Wr.Dec<Nat>) -> {FIn.get_tool.of(FIn.seq.fin(~Nat, ~Nat, i, d)) == Infer.ir.tool.p(i, d) : Wr.Dec<If.ToolPrio>}:
  match d:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ie.tool1(d: Wr.Dec<Nat>) -> {FIn.get_tool.of(FIn.seq(~Nat, ~Nat, ~Wr.get_nat, d)) == Infer.ir.tool.i(d) : Wr.Dec<If.ToolPrio>}:
  match d:
    case Wr.Got{+i, +s}:
      ie.tool2(i, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ie.tool(s: String) -> {FIn.get_tool(s) == Infer.ir.tool(s) : Wr.Dec<If.ToolPrio>}:
  ie.tool1(Wr.get_nat(s))

def ie.tools(+s: String) -> {FIn.get_tools(s) == Wr.get_list(~If.ToolPrio, ~Infer.ir.tool, s) : Wr.Dec<List<&2, If.ToolPrio>>}:
  LX.lx.get(~If.ToolPrio, ~FIn.get_tool, ~Infer.ir.tool, ~ie.tool, s)

def ie.req3(+cap: Maybe<&2, Nat>, +ts: List<&2, If.ToolPrio>, d: Wr.Dec<List<&2, Nat>>) -> {FIn.get_req.of(FIn.seq.fin(~FIn.P2<Maybe<&2, Nat>, List<&2, If.ToolPrio>>, ~List<&2, Nat>, FIn.P2{cap, ts}, d)) == Infer.ir.req.need(cap, ts, d) : Wr.Dec<FIn.Req>}:
  match d:
    case Wr.Got{need, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ie.req2(+cap: Maybe<&2, Nat>, d: Wr.Dec<List<&2, If.ToolPrio>>) -> {FIn.get_req.of(FIn.seq(~FIn.P2<Maybe<&2, Nat>, List<&2, If.ToolPrio>>, ~List<&2, Nat>, ~FIn.get_ids, FIn.seq.fin(~Maybe<&2, Nat>, ~List<&2, If.ToolPrio>, cap, d))) == Infer.ir.req.ts(cap, d) : Wr.Dec<FIn.Req>}:
  match d:
    case Wr.Got{+ts, +s}:
      ie.req3(cap, ts, FIn.get_ids(s))
    case Wr.Bad{}:
      {==}

def ie.req1(d: Wr.Dec<Maybe<&2, Nat>>) -> {FIn.get_req.of(FIn.seq(~FIn.P2<Maybe<&2, Nat>, List<&2, If.ToolPrio>>, ~List<&2, Nat>, ~FIn.get_ids, FIn.seq(~Maybe<&2, Nat>, ~List<&2, If.ToolPrio>, ~FIn.get_tools, d))) == Infer.ir.req.cap(d) : Wr.Dec<FIn.Req>}:
  match d:
    case Wr.Got{+cap, +s}:
      %ie.tools(s) : {FIn.get_req.of(FIn.seq(~FIn.P2<Maybe<&2, Nat>, List<&2, If.ToolPrio>>, ~List<&2, Nat>, ~FIn.get_ids, FIn.seq.fin(~Maybe<&2, Nat>, ~List<&2, If.ToolPrio>, cap, FIn.get_tools(s)))) == Infer.ir.req.ts(cap, _) : Wr.Dec<FIn.Req>}
      ie.req2(cap, FIn.get_tools(s))
    case Wr.Bad{}:
      {==}

def ie.req(+s: String) -> {FIn.get_req(s) == Infer.ir.read(s) : Wr.Dec<FIn.Req>}:
  %ie.mnat_go(Wr.get_nat(s)) : {FIn.get_req(s) == Infer.ir.req.cap(_) : Wr.Dec<FIn.Req>}
  ie.req1(FIn.get_mnat(s))

# Ordering facts
# --------------

# b not at most a: a at most b
def pin.flip(+a: Nat, +b: Nat, h: {Nat.is_le(b, a) == False{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogic.pq.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pin.flip(p, q, h)

# The merge sort is a stable sort
# -------------------------------

# x put before the first tool of priority at most x's (the laws' is.ins,
# with the model's priority)
def pis.ins(+x: If.ToolPrio, ys: List<&2, If.ToolPrio>) -> List<&2, If.ToolPrio>:
  match ys:
    case Nil{}:
      [x]
    case +y <> +yt:
      Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x)), x <> y <> yt, y <> pis.ins(x, yt))

def pis.sort(ts: List<&2, If.ToolPrio>) -> List<&2, If.ToolPrio>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      pis.ins(t, pis.sort(rest))

# a stable merge: the left list wins a tie
def pis.merge(xs: List<&2, If.ToolPrio>, ys: List<&2, If.ToolPrio>) -> List<&2, If.ToolPrio>:
  match xs ys:
    case Nil{} zs:
      zs
    case +x <> xt Nil{}:
      x <> xt
    case +x <> +xt +y <> +yt:
      Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x)), x <> pis.merge(xt, y <> yt), y <> pis.merge(x <> xt, yt))

def pi2.go(xt: List<&2, If.ToolPrio>, yt: List<&2, If.ToolPrio>, +x: If.ToolPrio, +y: If.ToolPrio, c: Bool) -> {If.tmerge.go(xt, yt, x, y, c) == Infer.is.if(List<&2, If.ToolPrio>, c, x <> pis.merge(xt, y <> yt), y <> pis.merge(x <> xt, yt)) : List<&2, If.ToolPrio>}:
  match xt yt c:
    case Nil{} Nil{} True{}:
      {==}
    case Nil{} Nil{} False{}:
      {==}
    case Nil{} y2 <> yt2 True{}:
      {==}
    case Nil{} +y2 <> +yt2 False{}:
      Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, z => y <> z, If.tmerge.go(Nil{}, yt2, x, y2, Nat.is_le(If.ToolPrio.prio(y2), If.ToolPrio.prio(x))), Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y2), If.ToolPrio.prio(x)), x <> pis.merge(Nil{}, y2 <> yt2), y2 <> pis.merge(x <> Nil{}, yt2)), pi2.go(Nil{}, yt2, x, y2, Nat.is_le(If.ToolPrio.prio(y2), If.ToolPrio.prio(x))))
    case +x2 <> +xt2 Nil{} True{}:
      Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, z => x <> z, If.tmerge.go(xt2, Nil{}, x2, y, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x2))), Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x2)), x2 <> pis.merge(xt2, y <> Nil{}), y <> pis.merge(x2 <> xt2, Nil{})), pi2.go(xt2, Nil{}, x2, y, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x2))))
    case x2 <> xt2 Nil{} False{}:
      {==}
    case +x2 <> +xt2 +y2 <> +yt2 True{}:
      Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, z => x <> z, If.tmerge.go(xt2, y2 <> yt2, x2, y, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x2))), Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x2)), x2 <> pis.merge(xt2, y <> y2 <> yt2), y <> pis.merge(x2 <> xt2, y2 <> yt2)), pi2.go(xt2, y2 <> yt2, x2, y, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x2))))
    case +x2 <> +xt2 +y2 <> +yt2 False{}:
      Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, z => y <> z, If.tmerge.go(x2 <> xt2, yt2, x, y2, Nat.is_le(If.ToolPrio.prio(y2), If.ToolPrio.prio(x))), Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y2), If.ToolPrio.prio(x)), x <> pis.merge(x2 <> xt2, y2 <> yt2), y2 <> pis.merge(x <> x2 <> xt2, yt2)), pi2.go(x2 <> xt2, yt2, x, y2, Nat.is_le(If.ToolPrio.prio(y2), If.ToolPrio.prio(x))))

def pi2.tmerge(xs: List<&2, If.ToolPrio>, ys: List<&2, If.ToolPrio>) -> {If.tmerge(xs, ys) == pis.merge(xs, ys) : List<&2, If.ToolPrio>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yt:
      {==}
    case x <> xt Nil{}:
      {==}
    case +x <> xt +y <> yt:
      pi2.go(xt, yt, x, y, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x)))

def pin.merge_nil_l(ys: List<&2, If.ToolPrio>) -> {pis.merge(Nil{}, ys) == ys : List<&2, If.ToolPrio>}:
  {==}

def pin.merge_nil_r(xs: List<&2, If.ToolPrio>) -> {pis.merge(xs, Nil{}) == xs : List<&2, If.ToolPrio>}:
  match xs:
    case Nil{}:
      {==}
    case x <> xt:
      {==}

# merging one tool is putting it in
def pin.n1(ys: List<&2, If.ToolPrio>, +x: If.ToolPrio) -> {pis.merge(x <> Nil{}, ys) == pis.ins(x, ys) : List<&2, If.ToolPrio>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +yt:
      %pin.n1(yt, x) : {Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x)), x <> pis.merge(Nil{}, y <> yt), y <> pis.merge(x <> Nil{}, yt)) == Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x)), x <> y <> yt, y <> _) : List<&2, If.ToolPrio>}
      {==}

def pin.nc(+a: If.ToolPrio, +at: List<&2, If.ToolPrio>, +b: If.ToolPrio, +bt: List<&2, If.ToolPrio>, +x: If.ToolPrio, cba: Bool, +eba: {Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)) == cba : Bool}, cax: Bool, +eax: {Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)) == cax : Bool}, cbx: Bool, +ebx: {Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(x)) == cbx : Bool}, +ih1: {pis.ins(x, pis.merge(at, b <> bt)) == pis.merge(pis.ins(x, at), b <> bt) : List<&2, If.ToolPrio>}, +ih2: {pis.ins(x, pis.merge(a <> at, bt)) == pis.merge(pis.ins(x, a <> at), bt) : List<&2, If.ToolPrio>}) -> {pis.ins(x, pis.merge(a <> at, b <> bt)) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}:
  match cba cax cbx:
    case True{} True{} True{}:
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), True{}, eba) : {pis.ins(x, Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(at, b <> bt), b <> pis.merge(a <> at, bt))) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), True{}, eax) : {Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> pis.merge(at, b <> bt), a <> pis.ins(x, pis.merge(at, b <> bt))) == pis.merge(Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> at, a <> pis.ins(x, at)), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(x)), True{}, ebx) : {x <> a <> pis.merge(at, b <> bt) == Infer.is.if(List<&2, If.ToolPrio>, _, x <> pis.merge(a <> at, b <> bt), b <> pis.merge(x <> a <> at, bt)) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), True{}, eba) : {x <> a <> pis.merge(at, b <> bt) == x <> Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(at, b <> bt), b <> pis.merge(a <> at, bt)) : List<&2, If.ToolPrio>}
      {==}
    case True{} True{} False{}:
      +tp = LNat.wn_le_trans(If.ToolPrio.prio(b), If.ToolPrio.prio(a), If.ToolPrio.prio(x), eba, eax)
      LLogic.pq.absurd({pis.ins(x, pis.merge(a <> at, b <> bt)) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}, Equal.trans(Bool, True{}, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(x)), False{}, Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(x)), True{}, tp), ebx))
    case True{} False{} True{}:
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), True{}, eba) : {pis.ins(x, Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(at, b <> bt), b <> pis.merge(a <> at, bt))) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), False{}, eax) : {Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> pis.merge(at, b <> bt), a <> pis.ins(x, pis.merge(at, b <> bt))) == pis.merge(Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> at, a <> pis.ins(x, at)), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), True{}, eba) : {a <> pis.ins(x, pis.merge(at, b <> bt)) == Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(pis.ins(x, at), b <> bt), b <> pis.merge(a <> pis.ins(x, at), bt)) : List<&2, If.ToolPrio>}
      Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, z => a <> z, pis.ins(x, pis.merge(at, b <> bt)), pis.merge(pis.ins(x, at), b <> bt), ih1)
    case True{} False{} False{}:
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), True{}, eba) : {pis.ins(x, Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(at, b <> bt), b <> pis.merge(a <> at, bt))) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), False{}, eax) : {Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> pis.merge(at, b <> bt), a <> pis.ins(x, pis.merge(at, b <> bt))) == pis.merge(Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> at, a <> pis.ins(x, at)), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), True{}, eba) : {a <> pis.ins(x, pis.merge(at, b <> bt)) == Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(pis.ins(x, at), b <> bt), b <> pis.merge(a <> pis.ins(x, at), bt)) : List<&2, If.ToolPrio>}
      Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, z => a <> z, pis.ins(x, pis.merge(at, b <> bt)), pis.merge(pis.ins(x, at), b <> bt), ih1)
    case False{} True{} True{}:
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), False{}, eba) : {pis.ins(x, Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(at, b <> bt), b <> pis.merge(a <> at, bt))) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(x)), True{}, ebx) : {Infer.is.if(List<&2, If.ToolPrio>, _, x <> b <> pis.merge(a <> at, bt), b <> pis.ins(x, pis.merge(a <> at, bt))) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), True{}, eax) : {x <> b <> pis.merge(a <> at, bt) == pis.merge(Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> at, a <> pis.ins(x, at)), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(x)), True{}, ebx) : {x <> b <> pis.merge(a <> at, bt) == Infer.is.if(List<&2, If.ToolPrio>, _, x <> pis.merge(a <> at, b <> bt), b <> pis.merge(x <> a <> at, bt)) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), False{}, eba) : {x <> b <> pis.merge(a <> at, bt) == x <> Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(at, b <> bt), b <> pis.merge(a <> at, bt)) : List<&2, If.ToolPrio>}
      {==}
    case False{} True{} False{}:
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), False{}, eba) : {pis.ins(x, Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(at, b <> bt), b <> pis.merge(a <> at, bt))) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(x)), False{}, ebx) : {Infer.is.if(List<&2, If.ToolPrio>, _, x <> b <> pis.merge(a <> at, bt), b <> pis.ins(x, pis.merge(a <> at, bt))) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), True{}, eax) : {b <> pis.ins(x, pis.merge(a <> at, bt)) == pis.merge(Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> at, a <> pis.ins(x, at)), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(x)), False{}, ebx) : {b <> pis.ins(x, pis.merge(a <> at, bt)) == Infer.is.if(List<&2, If.ToolPrio>, _, x <> pis.merge(a <> at, b <> bt), b <> pis.merge(x <> a <> at, bt)) : List<&2, If.ToolPrio>}
      %Equal.sym(List<&2, If.ToolPrio>, pis.ins(x, pis.merge(a <> at, bt)), pis.merge(pis.ins(x, a <> at), bt), ih2) : {b <> _ == b <> pis.merge(x <> a <> at, bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), True{}, eax) : {b <> pis.merge(Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> at, a <> pis.ins(x, at)), bt) == b <> pis.merge(x <> a <> at, bt) : List<&2, If.ToolPrio>}
      {==}
    case False{} False{} True{}:
      +ab = pin.flip(If.ToolPrio.prio(a), If.ToolPrio.prio(b), eba)
      +tp = LNat.wn_le_trans(If.ToolPrio.prio(a), If.ToolPrio.prio(b), If.ToolPrio.prio(x), ab, ebx)
      LLogic.pq.absurd({pis.ins(x, pis.merge(a <> at, b <> bt)) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}, Equal.trans(Bool, True{}, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), False{}, Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), True{}, tp), eax))
    case False{} False{} False{}:
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), False{}, eba) : {pis.ins(x, Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(at, b <> bt), b <> pis.merge(a <> at, bt))) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(x)), False{}, ebx) : {Infer.is.if(List<&2, If.ToolPrio>, _, x <> b <> pis.merge(a <> at, bt), b <> pis.ins(x, pis.merge(a <> at, bt))) == pis.merge(pis.ins(x, a <> at), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), False{}, eax) : {b <> pis.ins(x, pis.merge(a <> at, bt)) == pis.merge(Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> at, a <> pis.ins(x, at)), b <> bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), False{}, eba) : {b <> pis.ins(x, pis.merge(a <> at, bt)) == Infer.is.if(List<&2, If.ToolPrio>, _, a <> pis.merge(pis.ins(x, at), b <> bt), b <> pis.merge(a <> pis.ins(x, at), bt)) : List<&2, If.ToolPrio>}
      %Equal.sym(List<&2, If.ToolPrio>, pis.ins(x, pis.merge(a <> at, bt)), pis.merge(pis.ins(x, a <> at), bt), ih2) : {b <> _ == b <> pis.merge(a <> pis.ins(x, at), bt) : List<&2, If.ToolPrio>}
      %Equal.sym(Bool, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), False{}, eax) : {b <> pis.merge(Infer.is.if(List<&2, If.ToolPrio>, _, x <> a <> at, a <> pis.ins(x, at)), bt) == b <> pis.merge(a <> pis.ins(x, at), bt) : List<&2, If.ToolPrio>}
      {==}

# putting x into a merge is merging after putting x into the left list
def pin.n(xs: List<&2, If.ToolPrio>, ys: List<&2, If.ToolPrio>, +x: If.ToolPrio) -> {pis.ins(x, pis.merge(xs, ys)) == pis.merge(pis.ins(x, xs), ys) : List<&2, If.ToolPrio>}:
  match xs ys:
    case Nil{} +zs:
      Equal.trans(List<&2, If.ToolPrio>, pis.ins(x, pis.merge(Nil{}, zs)), pis.ins(x, zs), pis.merge(x <> Nil{}, zs), Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, w => pis.ins(x, w), pis.merge(Nil{}, zs), zs, pin.merge_nil_l(zs)), Equal.sym(List<&2, If.ToolPrio>, pis.merge(x <> Nil{}, zs), pis.ins(x, zs), pin.n1(zs, x)))
    case +a <> +at Nil{}:
      Equal.sym(List<&2, If.ToolPrio>, pis.merge(pis.ins(x, a <> at), Nil{}), pis.ins(x, a <> at), pin.merge_nil_r(pis.ins(x, a <> at)))
    case +a <> +at +b <> +bt:
      pin.nc(a, at, b, bt, x, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(a)), {==}, Nat.is_le(If.ToolPrio.prio(a), If.ToolPrio.prio(x)), {==}, Nat.is_le(If.ToolPrio.prio(b), If.ToolPrio.prio(x)), {==}, pin.n(at, b <> bt, x), pin.n(a <> at, bt, x))

# merging two sorted lists sorts their concatenation
def pin.msort(xs: List<&2, If.ToolPrio>, +ys: List<&2, If.ToolPrio>) -> {pis.merge(pis.sort(xs), pis.sort(ys)) == pis.sort(List.append(&2, If.ToolPrio, xs, ys)) : List<&2, If.ToolPrio>}:
  match xs:
    case Nil{}:
      pin.merge_nil_l(pis.sort(ys))
    case +x <> +rest:
      Equal.trans(List<&2, If.ToolPrio>, pis.merge(pis.ins(x, pis.sort(rest)), pis.sort(ys)), pis.ins(x, pis.merge(pis.sort(rest), pis.sort(ys))), pis.ins(x, pis.sort(List.append(&2, If.ToolPrio, rest, ys))), Equal.sym(List<&2, If.ToolPrio>, pis.ins(x, pis.merge(pis.sort(rest), pis.sort(ys))), pis.merge(pis.ins(x, pis.sort(rest)), pis.sort(ys)), pin.n(pis.sort(rest), pis.sort(ys), x)), Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, w => pis.ins(x, w), pis.merge(pis.sort(rest), pis.sort(ys)), pis.sort(List.append(&2, If.ToolPrio, rest, ys)), pin.msort(rest, ys)))

# The counter keeps the tools in order
# ------------------------------------

def pin.app_nil(xs: List<&2, If.ToolPrio>) -> {List.append(&2, If.ToolPrio, xs, Nil{}) == xs : List<&2, If.ToolPrio>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, w => x <> w, List.append(&2, If.ToolPrio, rest, Nil{}), rest, pin.app_nil(rest))

def pin.app_assoc(xs: List<&2, If.ToolPrio>, +ys: List<&2, If.ToolPrio>, +zs: List<&2, If.ToolPrio>) -> {List.append(&2, If.ToolPrio, List.append(&2, If.ToolPrio, xs, ys), zs) == List.append(&2, If.ToolPrio, xs, List.append(&2, If.ToolPrio, ys, zs)) : List<&2, If.ToolPrio>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, w => x <> w, List.append(&2, If.ToolPrio, List.append(&2, If.ToolPrio, rest, ys), zs), List.append(&2, If.ToolPrio, rest, List.append(&2, If.ToolPrio, ys, zs)), pin.app_assoc(rest, ys, zs))

# the leaves of a tree, left to right
def pin.lv(t: If.TTree) -> List<&2, If.ToolPrio>:
  match t:
    case If.TTip{}:
      Nil{}
    case If.TLeaf{u}:
      [u]
    case If.TNode{l, r}:
      List.append(&2, If.ToolPrio, pin.lv(l), pin.lv(r))

# the leaves of a counter: the highest digit (the earliest tools) first
def pin.dl(ds: If.TDig) -> List<&2, If.ToolPrio>:
  match ds:
    case If.TEnd{}:
      Nil{}
    case If.T0{r}:
      pin.dl(r)
    case If.T1{t, r}:
      List.append(&2, If.ToolPrio, pin.dl(r), pin.lv(t))

def pin.join(ds: If.TDig, +acc: If.TTree) -> {pin.lv(If.tjoin(ds, acc)) == List.append(&2, If.ToolPrio, pin.dl(ds), pin.lv(acc)) : List<&2, If.ToolPrio>}:
  match ds:
    case If.TEnd{}:
      {==}
    case If.T0{r}:
      pin.join(r, acc)
    case If.T1{+t, +r}:
      Equal.trans(List<&2, If.ToolPrio>, pin.lv(If.tjoin(r, If.TNode{t, acc})), List.append(&2, If.ToolPrio, pin.dl(r), List.append(&2, If.ToolPrio, pin.lv(t), pin.lv(acc))), List.append(&2, If.ToolPrio, List.append(&2, If.ToolPrio, pin.dl(r), pin.lv(t)), pin.lv(acc)), pin.join(r, If.TNode{t, acc}), Equal.sym(List<&2, If.ToolPrio>, List.append(&2, If.ToolPrio, List.append(&2, If.ToolPrio, pin.dl(r), pin.lv(t)), pin.lv(acc)), List.append(&2, If.ToolPrio, pin.dl(r), List.append(&2, If.ToolPrio, pin.lv(t), pin.lv(acc))), pin.app_assoc(pin.dl(r), pin.lv(t), pin.lv(acc))))

def pin.push(ds: If.TDig, +t: If.TTree) -> {pin.dl(If.tpush(ds, t)) == List.append(&2, If.ToolPrio, pin.dl(ds), pin.lv(t)) : List<&2, If.ToolPrio>}:
  match ds:
    case If.TEnd{}:
      {==}
    case If.T0{r}:
      {==}
    case If.T1{+t2, +r}:
      Equal.trans(List<&2, If.ToolPrio>, pin.dl(If.tpush(r, If.TNode{t2, t})), List.append(&2, If.ToolPrio, pin.dl(r), List.append(&2, If.ToolPrio, pin.lv(t2), pin.lv(t))), List.append(&2, If.ToolPrio, List.append(&2, If.ToolPrio, pin.dl(r), pin.lv(t2)), pin.lv(t)), pin.push(r, If.TNode{t2, t}), Equal.sym(List<&2, If.ToolPrio>, List.append(&2, If.ToolPrio, List.append(&2, If.ToolPrio, pin.dl(r), pin.lv(t2)), pin.lv(t)), List.append(&2, If.ToolPrio, pin.dl(r), List.append(&2, If.ToolPrio, pin.lv(t2), pin.lv(t))), pin.app_assoc(pin.dl(r), pin.lv(t2), pin.lv(t))))

def pin.build(ts: List<&2, If.ToolPrio>, +ds: If.TDig) -> {pin.dl(If.tbuild(ts, ds)) == List.append(&2, If.ToolPrio, pin.dl(ds), ts) : List<&2, If.ToolPrio>}:
  match ts:
    case Nil{}:
      Equal.sym(List<&2, If.ToolPrio>, List.append(&2, If.ToolPrio, pin.dl(ds), Nil{}), pin.dl(ds), pin.app_nil(pin.dl(ds)))
    case +t <> +rest:
      +P = If.tpush(ds, If.TLeaf{t})
      Equal.trans(List<&2, If.ToolPrio>, pin.dl(If.tbuild(rest, P)), List.append(&2, If.ToolPrio, pin.dl(P), rest), List.append(&2, If.ToolPrio, pin.dl(ds), t <> rest), pin.build(rest, P), Equal.trans(List<&2, If.ToolPrio>, List.append(&2, If.ToolPrio, pin.dl(P), rest), List.append(&2, If.ToolPrio, List.append(&2, If.ToolPrio, pin.dl(ds), [t]), rest), List.append(&2, If.ToolPrio, pin.dl(ds), t <> rest), Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, w => List.append(&2, If.ToolPrio, w, rest), pin.dl(P), List.append(&2, If.ToolPrio, pin.dl(ds), [t]), pin.push(ds, If.TLeaf{t})), pin.app_assoc(pin.dl(ds), [t], rest)))

def pin.tsort(t: If.TTree) -> {If.tsort(t) == pis.sort(pin.lv(t)) : List<&2, If.ToolPrio>}:
  match t:
    case If.TTip{}:
      {==}
    case If.TLeaf{u}:
      {==}
    case If.TNode{+l, +r}:
      +sl = pis.sort(pin.lv(l))
      +sr = pis.sort(pin.lv(r))
      +c1 = Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, w => pis.merge(w, If.tsort(r)), If.tsort(l), sl, pin.tsort(l))
      +c2 = Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, w => pis.merge(sl, w), If.tsort(r), sr, pin.tsort(r))
      +m = Equal.trans(List<&2, If.ToolPrio>, pis.merge(If.tsort(l), If.tsort(r)), pis.merge(sl, If.tsort(r)), pis.merge(sl, sr), c1, c2)
      Equal.trans(List<&2, If.ToolPrio>, If.tmerge(If.tsort(l), If.tsort(r)), pis.merge(If.tsort(l), If.tsort(r)), pis.sort(List.append(&2, If.ToolPrio, pin.lv(l), pin.lv(r))), pi2.tmerge(If.tsort(l), If.tsort(r)), Equal.trans(List<&2, If.ToolPrio>, pis.merge(If.tsort(l), If.tsort(r)), pis.merge(sl, sr), pis.sort(List.append(&2, If.ToolPrio, pin.lv(l), pin.lv(r))), m, pin.msort(pin.lv(l), pin.lv(r))))

def pin.rank(+ts: List<&2, If.ToolPrio>) -> {If.rank(ts) == pis.sort(ts) : List<&2, If.ToolPrio>}:
  +B = If.tbuild(ts, If.TEnd{})
  +J = If.tjoin(B, If.TTip{})
  +lvj = Equal.trans(List<&2, If.ToolPrio>, pin.lv(J), List.append(&2, If.ToolPrio, pin.dl(B), Nil{}), ts, pin.join(B, If.TTip{}), Equal.trans(List<&2, If.ToolPrio>, List.append(&2, If.ToolPrio, pin.dl(B), Nil{}), pin.dl(B), ts, pin.app_nil(pin.dl(B)), pin.build(ts, If.TEnd{})))
  Equal.trans(List<&2, If.ToolPrio>, If.tsort(J), pis.sort(pin.lv(J)), pis.sort(ts), pin.tsort(J), Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, w => pis.sort(w), pin.lv(J), ts, lvj))

# The plan
# --------

def pin.id(t: If.ToolPrio) -> {If.ToolPrio.id(t) == Infer.is.id(t) : Nat}:
  match t:
    case If.ToolPrio{i, p}:
      {==}

def pin.prio(t: If.ToolPrio) -> {If.ToolPrio.prio(t) == Infer.is.prio(t) : Nat}:
  match t:
    case If.ToolPrio{i, p}:
      {==}

def pin.ins_spec(+x: If.ToolPrio, ys: List<&2, If.ToolPrio>) -> {pis.ins(x, ys) == Infer.is.ins(x, ys) : List<&2, If.ToolPrio>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +yt:
      %pin.ins_spec(x, yt) : {Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x)), x <> y <> yt, y <> pis.ins(x, yt)) == Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(Infer.is.prio(y), Infer.is.prio(x)), x <> y <> yt, y <> _) : List<&2, If.ToolPrio>}
      %pin.prio(y) : {Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x)), x <> y <> yt, y <> pis.ins(x, yt)) == Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(_, Infer.is.prio(x)), x <> y <> yt, y <> pis.ins(x, yt)) : List<&2, If.ToolPrio>}
      %pin.prio(x) : {Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y), If.ToolPrio.prio(x)), x <> y <> yt, y <> pis.ins(x, yt)) == Infer.is.if(List<&2, If.ToolPrio>, Nat.is_le(If.ToolPrio.prio(y), _), x <> y <> yt, y <> pis.ins(x, yt)) : List<&2, If.ToolPrio>}
      {==}

def pin.sort_spec(ts: List<&2, If.ToolPrio>) -> {pis.sort(ts) == Infer.is.sort(ts) : List<&2, If.ToolPrio>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      %pin.sort_spec(rest) : {pis.ins(t, pis.sort(rest)) == Infer.is.ins(t, _) : List<&2, If.ToolPrio>}
      pin.ins_spec(t, pis.sort(rest))

def pin.elem(xs: List<&2, Nat>, +x: Nat) -> {If.elem(xs, x) == Infer.is.elem(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      %pin.elem(rest, x) : {If.elem(y <> rest, x) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def pin.needs_step(b: Bool, +t: If.ToolPrio, +rest: List<&2, If.ToolPrio>, +need: List<&2, Nat>) -> {If.needs.go(t <> rest, need, b) == Infer.is.if(Maybe<&2, Nat>, b, Some{If.ToolPrio.id(t)}, If.needs.go(rest, need, If.needs.at(rest, need))) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pin.needs(ls: List<&2, If.ToolPrio>, +need: List<&2, Nat>) -> {If.needs.go(ls, need, If.needs.at(ls, need)) == Infer.is.needed(ls, need) : Maybe<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case +t <> +rest:
      %pin.needs(rest, need) : {If.needs.go(t <> rest, need, If.elem(need, If.ToolPrio.id(t))) == Infer.is.if(Maybe<&2, Nat>, Infer.is.elem(need, Infer.is.id(t)), Some{Infer.is.id(t)}, _) : Maybe<&2, Nat>}
      %pin.id(t) : {If.needs.go(t <> rest, need, If.elem(need, If.ToolPrio.id(t))) == Infer.is.if(Maybe<&2, Nat>, Infer.is.elem(need, _), Some{_}, If.needs.go(rest, need, If.needs.at(rest, need))) : Maybe<&2, Nat>}
      %pin.elem(need, If.ToolPrio.id(t)) : {If.needs.go(t <> rest, need, If.elem(need, If.ToolPrio.id(t))) == Infer.is.if(Maybe<&2, Nat>, _, Some{If.ToolPrio.id(t)}, If.needs.go(rest, need, If.needs.at(rest, need))) : Maybe<&2, Nat>}
      pin.needs_step(If.elem(need, If.ToolPrio.id(t)), t, rest, need)

def pin.ids(ts: List<&2, If.ToolPrio>) -> {If.ids(ts) == Infer.is.ids(ts) : List<&2, Nat>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      %pin.ids(rest) : {If.ids(t <> rest) == Infer.is.id(t) <> _ : List<&2, Nat>}
      %pin.id(t) : {If.ids(t <> rest) == _ <> If.ids(rest) : List<&2, Nat>}
      {==}

def pin.plan_of(m: Maybe<&2, Nat>, +loose: List<&2, If.ToolPrio>) -> {If.plan.of(m, loose) == Infer.is.plan.of(m, loose) : If.Plan}:
  match m:
    case Some{i}:
      {==}
    case None{}:
      Equal.cong(List<&2, Nat>, If.Plan, w => If.Fits{w}, If.ids(loose), Infer.is.ids(loose), pin.ids(loose))

def pin.loose(+cap: Maybe<&2, Nat>, +ts: List<&2, If.ToolPrio>) -> {Pair.snd(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(cap, ts)) == Infer.is.loose(cap, ts) : List<&2, If.ToolPrio>}:
  match cap:
    case None{}:
      {==}
    case Some{+c}:
      Equal.cong(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, w => List.drop(&2, If.ToolPrio, w, c), If.rank(ts), Infer.is.sort(ts), Equal.trans(List<&2, If.ToolPrio>, If.rank(ts), pis.sort(ts), Infer.is.sort(ts), pin.rank(ts), pin.sort_spec(ts)))

def pin.plan(+cap: Maybe<&2, Nat>, +ts: List<&2, If.ToolPrio>, +need: List<&2, Nat>) -> {If.plan(cap, ts, need) == Infer.is.plan(cap, ts, need) : If.Plan}:
  +lo = Infer.is.loose(cap, ts)
  %Equal.sym(List<&2, If.ToolPrio>, Pair.snd(List<&2, If.ToolPrio>, List<&2, If.ToolPrio>, If.strict.of(cap, ts)), lo, pin.loose(cap, ts)) : {If.plan.loose(_, need) == Infer.is.plan(cap, ts, need) : If.Plan}
  %pin.needs(lo, need) : {If.plan.loose(lo, need) == Infer.is.plan.of(_, lo) : If.Plan}
  pin.plan_of(If.needs.go(lo, need, If.needs.at(lo, need)), lo)

# Spelling and the entry
# ----------------------

def ie.put_plan(p: If.Plan) -> {FIn.put_plan(p, "") == Infer.is.put_plan(p) : String}:
  match p:
    case If.Fits{ls}:
      {==}
    case If.Over{i}:
      {==}

def ie.end(b: Bool, q: FIn.Req) -> {FIn.ffi.done(b, q) == Infer.is.end(b, q) : String}:
  match b:
    case True{}:
      match q:
        case FIn.Req{+cap, +ts, +need}:
          %pin.plan(cap, ts, need) : {FIn.put_plan(If.plan(cap, ts, need), "") == Infer.is.put_plan(_) : String}
          ie.put_plan(If.plan(cap, ts, need))
    case False{}:
      {==}

def ie.run(r: Wr.Dec<FIn.Req>) -> {FIn.ffi.go(r) == Infer.is.run(r) : String}:
  match r:
    case Wr.Got{q, +s}:
      ie.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def Infer.core_infer_ffi_exact(s):
  %ie.req(s) : {FIn.ffi.go(FIn.get_req(s)) == Infer.is.run(_) : String}
  ie.run(FIn.get_req(s))
