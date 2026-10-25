# eukhe: lemmas of the entry proofs of area compaction_cut: only spelled
# requests decode
#
# Each decoder of bend/ffi_compaction_cut.bend answers Got only for the
# spec's spelling of a value whose numbers fit (the messages, stop
# reasons, Nats and Bools: proof/context_order/base/exact.bend; strings:
# wire_str_exact, wire_str_decoded_fits).

import Base
import ../../../bend/context_order.bend as Co
import ../../../bend/ffi_context_order.bend as FCo
import ../../../bend/compaction_cut.bend as Cc
import ../../../bend/ffi_compaction_cut.bend as FCc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/context_order.bend as ContextOrder
import ../../../laws/compaction_cut.bend as CompactionCut
import ../../context_order/base.bend as LACo
import ../../context_order/base/read.bend as LACoRead
import ../../context_order/base/exact.bend as LACoExact
import ../../context_order/base/reply.bend as LACoReply

def cce.PS(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{+a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cce.ps_go(+s: String, d: Wr.Dec<String>, +ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> cce.PS(s, d):
  match d:
    case Wr.Got{+a, +r}:
      (Wire.wire_str_exact(s, a, r, ed), Wire.wire_str_decoded_fits(s, a, r, ed))
    case Wr.Bad{}:
      Unit{}

def cce.ps(+s: String) -> cce.PS(s, Wr.get_str(s)):
  cce.ps_go(s, Wr.get_str(s), {==})

def cce.LI(s: String, d: Wr.Dec<Cc.Limit>) -> Type:
  match d:
    case Wr.Got{+l, r}:
      {s == CompactionCut.spell_limit(l, r) : String} & {CompactionCut.limit_fits(l) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cce.li.k(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s1, d)) -> cce.LI(s, FCc.get_limit.k(d)):
  match d:
    case Wr.Got{+k, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(k, r)), e0, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(k, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def cce.li.top(-s: String, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s, d)) -> cce.LI(s, FCc.get_limit.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          (e0, {==})
        case 1n:
          (e0, f0) = p
          cce.li.k(s, s1, e0, Wr.get_nat(s1), LACoExact.coe.pnf(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def cce.limit(+s: String) -> cce.LI(s, FCc.get_limit(s)):
  cce.li.top(s, Wr.get_nat(s), LACoExact.coe.pnf(s))

def cce.CO(s: String, d: Wr.Dec<Cc.Contrib>) -> Type:
  match d:
    case Wr.Got{+c, r}:
      {s == CompactionCut.spell_contrib(c, r) : String} & {CompactionCut.contrib_fits(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cce.co.ms(-s: String, -s1: String, +tok: Nat, e0: {s == Wr.put_nat(tok, s1) : String}, ft: {LawsBase.wire_fits(tok) == True{} : Bool}, d: Wr.Dec<List<&2, Co.Msg>>, p: LACoExact.coe.ml.LS(s1, d)) -> cce.CO(s, FCc.get_contrib.ms(tok, d)):
  match d:
    case Wr.Got{+ms, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(tok, s1), Wr.put_nat(tok, ContextOrder.spell_msgs(ms, r)), e0, Equal.cong(String, String, z => Wr.put_nat(tok, z), s1, ContextOrder.spell_msgs(ms, r), e1)), LACo.co.and_tt(LawsBase.wire_fits(tok), ContextOrder.msgs_fit(ms), ft, f1))
    case Wr.Bad{}:
      Unit{}

def cce.co.tok(-s: String, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s, d)) -> cce.CO(s, FCc.get_contrib.tokens(d)):
  match d:
    case Wr.Got{+tok, +s1}:
      (e0, f0) = p
      cce.co.ms(s, s1, tok, e0, f0, FCo.get_msgs(s1), LACoExact.coe.ml.list(s1))
    case Wr.Bad{}:
      Unit{}

# a contribution decoded is spelled, and its numbers fit
def cce.contrib(+s: String) -> cce.CO(s, FCc.get_contrib(s)):
  cce.co.tok(s, Wr.get_nat(s), LACoExact.coe.pnf(s))

# what the item loop over Cc.Contrib answers says about its input s (m + 1 items)
def cce.cl.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Cc.Contrib>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == CompactionCut.spell_contribs.items(xs, r) : String} & ({List.length(&2, Cc.Contrib, xs) == 1n+m : Nat} & {CompactionCut.contribs_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def cce.cl.step(-s: String, +x: Cc.Contrib, +s3: String, -k: Nat, ex: {s == CompactionCut.spell_contrib(x, s3) : String}, fx: {CompactionCut.contrib_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Cc.Contrib>>, ih: cce.cl.PL(s3, k, d)) -> cce.cl.PL(s, 1n+k, Wr.get_list.cons(Cc.Contrib, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, rest) = ih
      (e2, e3) = rest
      (Equal.trans(String, s, CompactionCut.spell_contrib(x, s3), CompactionCut.spell_contrib(x, CompactionCut.spell_contribs.items(ys, r)), ex, Equal.cong(String, String, z => CompactionCut.spell_contrib(x, z), s3, CompactionCut.spell_contribs.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Cc.Contrib, ys), 1n+k, e2), LACo.co.and_tt(CompactionCut.contrib_fits(x), CompactionCut.contribs_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items whose numbers fit
def cce.cl.loop(m: Nat, cur: Wr.Dec<Cc.Contrib>, +s: String, pc: cce.CO(s, cur)) -> cce.cl.PL(s, m, Wr.get_list.go(~Cc.Contrib, ~FCc.get_contrib, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LACo.co.and_tt(CompactionCut.contrib_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      cce.cl.step(s, x, s3, k, e, f, Wr.get_list.go(~Cc.Contrib, ~FCc.get_contrib, k, FCc.get_contrib(s3)), cce.cl.loop(k, FCc.get_contrib(s3), s3, cce.contrib(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def cce.cl.LS(s: String, d: Wr.Dec<List<&2, Cc.Contrib>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Cc.Contrib, xs), CompactionCut.spell_contribs.items(xs, r)) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Cc.Contrib, xs)), CompactionCut.contribs_all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cce.cl.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Cc.Contrib>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == CompactionCut.spell_contribs.items(xs, r) : String}, e2: {List.length(&2, Cc.Contrib, xs) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, Cc.Contrib, xs), CompactionCut.spell_contribs.items(xs, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Cc.Contrib, xs), 1n+m, e2) : {s == Wr.put_nat(_, CompactionCut.spell_contribs.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def cce.cl.conv_f(+m: Nat, +xs: List<&2, Cc.Contrib>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Cc.Contrib, xs) == 1n+m : Nat}, e3: {CompactionCut.contribs_all(xs) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Cc.Contrib, xs)), CompactionCut.contribs_all(xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Cc.Contrib, xs), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), CompactionCut.contribs_all(xs)) == True{} : Bool}
  LACo.co.and_tt(LawsBase.wire_fits(1n+m), CompactionCut.contribs_all(xs), fn, e3)

def cce.cl.conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Cc.Contrib>>, pl: cce.cl.PL(s2, m, d)) -> cce.cl.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, rest) = pl
      (+e2, e3) = rest
      (cce.cl.conv_s(s, s2, m, xs, r, en, e1, e2), cce.cl.conv_f(m, xs, fn, e2, e3))
    case Wr.Bad{}:
      Unit{}

def cce.cl.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> cce.cl.LS(s, Wr.get_list.start(~Cc.Contrib, ~FCc.get_contrib, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      cce.cl.conv(s, s2, m, en, fn, Wr.get_list.go(~Cc.Contrib, ~FCc.get_contrib, m, FCc.get_contrib(s2)), cce.cl.loop(m, FCc.get_contrib(s2), s2, cce.contrib(s2)))

def cce.cl.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cce.cl.LS(s, Wr.get_list.start(~Cc.Contrib, ~FCc.get_contrib, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      cce.cl.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of Cc.Contrib decoded is spelled, and its count and items fit
def cce.cl.list(+s: String) -> cce.cl.LS(s, Wr.get_list(~Cc.Contrib, ~FCc.get_contrib, s)):
  cce.cl.top(s, Wr.get_nat(s), {==})

def cce.ER(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{+m, r}:
      {s == CompactionCut.spell_err(m, r) : String} & {CompactionCut.err_fits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cce.er.text(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, p: cce.PS(s1, d)) -> cce.ER(s, FCc.get_err.text(d)):
  match d:
    case Wr.Got{+a, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(a, r)), e0, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_str(a, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def cce.er.top(-s: String, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s, d)) -> cce.ER(s, FCc.get_err.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          (e0, {==})
        case 1n:
          (e0, f0) = p
          cce.er.text(s, s1, e0, Wr.get_str(s1), cce.ps(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def cce.err(+s: String) -> cce.ER(s, FCc.get_err(s)):
  cce.er.top(s, Wr.get_nat(s), LACoExact.coe.pnf(s))

# ---- requests ----

def cce.RQ(s: String, d: Wr.Dec<FCc.Req>) -> Type:
  match d:
    case Wr.Got{+q, r}:
      {s == CompactionCut.spell_req(q, r) : String} & {CompactionCut.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cce.rq.cs(-s: String, -s3: String, +hd: Bool, +l: Cc.Limit, e0: {s == Wr.put_nat(0n, Wr.put_bool(hd, CompactionCut.spell_limit(l, s3))) : String}, fl: {CompactionCut.limit_fits(l) == True{} : Bool}, d: Wr.Dec<List<&2, Cc.Contrib>>, p: cce.cl.LS(s3, d)) -> cce.RQ(s, FCc.get_cut.cs(hd, l, d)):
  match d:
    case Wr.Got{+cs, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(hd, CompactionCut.spell_limit(l, s3))), Wr.put_nat(0n, Wr.put_bool(hd, CompactionCut.spell_limit(l, Wr.put_nat(List.length(&2, Cc.Contrib, cs), CompactionCut.spell_contribs.items(cs, r))))), e0, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(hd, CompactionCut.spell_limit(l, z))), s3, Wr.put_nat(List.length(&2, Cc.Contrib, cs), CompactionCut.spell_contribs.items(cs, r)), e1)), LACo.co.and_tt(CompactionCut.limit_fits(l), Bool.and(LawsBase.wire_fits(List.length(&2, Cc.Contrib, cs)), CompactionCut.contribs_all(cs)), fl, f1))
    case Wr.Bad{}:
      Unit{}

def cce.rq.lim(-s: String, -s2: String, +hd: Bool, e0: {s == Wr.put_nat(0n, Wr.put_bool(hd, s2)) : String}, d: Wr.Dec<Cc.Limit>, p: cce.LI(s2, d)) -> cce.RQ(s, FCc.get_cut.lim(hd, d)):
  match d:
    case Wr.Got{+l, +s3}:
      (e1, f1) = p
      cce.rq.cs(s, s3, hd, l, Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(hd, s2)), Wr.put_nat(0n, Wr.put_bool(hd, CompactionCut.spell_limit(l, s3))), e0, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(hd, z)), s2, CompactionCut.spell_limit(l, s3), e1)), f1, Wr.get_list(~Cc.Contrib, ~FCc.get_contrib, s3), cce.cl.list(s3))
    case Wr.Bad{}:
      Unit{}

def cce.rq.cut(-s: String, -s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Bool>, p: LACoExact.coe.PB(s1, d)) -> cce.RQ(s, FCc.get_cut(d)):
  match d:
    case Wr.Got{+hd, +s2}:
      cce.rq.lim(s, s2, hd, Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_bool(hd, s2)), e0, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_bool(hd, s2), p)), FCc.get_limit(s2), cce.limit(s2))
    case Wr.Bad{}:
      Unit{}

def cce.rq.err(-s: String, -s4: String, +st: Co.Stop, +c: Bool, +x: Bool, e0: {s == Wr.put_nat(1n, ContextOrder.spell_stop(st, Wr.put_bool(c, Wr.put_bool(x, s4)))) : String}, d: Wr.Dec<Maybe<&2, String>>, p: cce.ER(s4, d)) -> cce.RQ(s, FCc.get_summary.err(st, c, x, d)):
  match d:
    case Wr.Got{+e, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(1n, ContextOrder.spell_stop(st, Wr.put_bool(c, Wr.put_bool(x, s4)))), Wr.put_nat(1n, ContextOrder.spell_stop(st, Wr.put_bool(c, Wr.put_bool(x, CompactionCut.spell_err(e, r))))), e0, Equal.cong(String, String, z => Wr.put_nat(1n, ContextOrder.spell_stop(st, Wr.put_bool(c, Wr.put_bool(x, z)))), s4, CompactionCut.spell_err(e, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def cce.rq.text(-s: String, -s3: String, +st: Co.Stop, +c: Bool, e0: {s == Wr.put_nat(1n, ContextOrder.spell_stop(st, Wr.put_bool(c, s3))) : String}, d: Wr.Dec<Bool>, p: LACoExact.coe.PB(s3, d)) -> cce.RQ(s, FCc.get_summary.text(st, c, d)):
  match d:
    case Wr.Got{+x, +s4}:
      cce.rq.err(s, s4, st, c, x, Equal.trans(String, s, Wr.put_nat(1n, ContextOrder.spell_stop(st, Wr.put_bool(c, s3))), Wr.put_nat(1n, ContextOrder.spell_stop(st, Wr.put_bool(c, Wr.put_bool(x, s4)))), e0, Equal.cong(String, String, z => Wr.put_nat(1n, ContextOrder.spell_stop(st, Wr.put_bool(c, z))), s3, Wr.put_bool(x, s4), p)), FCc.get_err(s4), cce.err(s4))
    case Wr.Bad{}:
      Unit{}

def cce.rq.calls(-s: String, -s2: String, +st: Co.Stop, e0: {s == Wr.put_nat(1n, ContextOrder.spell_stop(st, s2)) : String}, d: Wr.Dec<Bool>, p: LACoExact.coe.PB(s2, d)) -> cce.RQ(s, FCc.get_summary.calls(st, d)):
  match d:
    case Wr.Got{+c, +s3}:
      cce.rq.text(s, s3, st, c, Equal.trans(String, s, Wr.put_nat(1n, ContextOrder.spell_stop(st, s2)), Wr.put_nat(1n, ContextOrder.spell_stop(st, Wr.put_bool(c, s3))), e0, Equal.cong(String, String, z => Wr.put_nat(1n, ContextOrder.spell_stop(st, z)), s2, Wr.put_bool(c, s3), p)), Wr.get_bool(s3), LACoExact.coe.pb(s3))
    case Wr.Bad{}:
      Unit{}

def cce.rq.stop(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Co.Stop>, p: LACoExact.coe.ST(s1, d)) -> cce.RQ(s, FCc.get_summary(d)):
  match d:
    case Wr.Got{+st, +s2}:
      cce.rq.calls(s, s2, st, Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, ContextOrder.spell_stop(st, s2)), e0, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, ContextOrder.spell_stop(st, s2), p)), Wr.get_bool(s2), LACoExact.coe.pb(s2))
    case Wr.Bad{}:
      Unit{}

def cce.rq.top(-s: String, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s, d)) -> cce.RQ(s, FCc.get_req.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          cce.rq.cut(s, s1, e0, Wr.get_bool(s1), LACoExact.coe.pb(s1))
        case 1n:
          (e0, f0) = p
          cce.rq.stop(s, s1, e0, FCo.get_stop(s1), LACoExact.coe.stop(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and its numbers fit
def cce.req(+s: String) -> cce.RQ(s, FCc.get_req(s)):
  cce.rq.top(s, Wr.get_nat(s), LACoExact.coe.pnf(s))
