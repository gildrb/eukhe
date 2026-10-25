# eukhe: lemmas of the entry proofs of area compaction_cut: spelled
# requests read back
#
# Each decoder of bend/ffi_compaction_cut.bend reads the spec's spelling
# of a value whose numbers fit back and leaves the rest untouched (the
# messages and stop reasons: proof/context_order/base/read.bend).

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

def cct.limit(l: Cc.Limit, +rest: String, +h: {CompactionCut.limit_fits(l) == True{} : Bool}) -> {FCc.get_limit(CompactionCut.spell_limit(l, rest)) == Wr.Got{l, rest} : Wr.Dec<Cc.Limit>}:
  match l:
    case Cc.Never{}:
      %LACoRead.cot.nat(0n, rest, {==}) : {FCc.get_limit.tag(_) == Wr.Got{Cc.Never{}, rest} : Wr.Dec<Cc.Limit>}
      {==}
    case Cc.Below{+k}:
      %LACoRead.cot.nat(1n, Wr.put_nat(k, rest), {==}) : {FCc.get_limit.tag(_) == Wr.Got{Cc.Below{k}, rest} : Wr.Dec<Cc.Limit>}
      %LACoRead.cot.nat(k, rest, h) : {FCc.get_limit.k(_) == Wr.Got{Cc.Below{k}, rest} : Wr.Dec<Cc.Limit>}
      {==}

def cct.contrib(c: Cc.Contrib, +rest: String, +h: {CompactionCut.contrib_fits(c) == True{} : Bool}) -> {FCc.get_contrib(CompactionCut.spell_contrib(c, rest)) == Wr.Got{c, rest} : Wr.Dec<Cc.Contrib>}:
  match c:
    case Cc.Contrib{+tok, +ms}:
      %LACoRead.cot.nat(tok, ContextOrder.spell_msgs(ms, rest), LACo.co.and_l(LawsBase.wire_fits(tok), ContextOrder.msgs_fit(ms), h)) : {FCc.get_contrib.tokens(_) == Wr.Got{Cc.Contrib{tok, ms}, rest} : Wr.Dec<Cc.Contrib>}
      %Equal.sym(Wr.Dec<List<&2, Co.Msg>>, FCo.get_msgs(ContextOrder.spell_msgs(ms, rest)), Wr.Got{ms, rest}, LACoRead.cot.ml.rt(ms, rest, LACo.co.and_r(LawsBase.wire_fits(tok), ContextOrder.msgs_fit(ms), h))) : {FCc.get_contrib.ms(tok, _) == Wr.Got{Cc.Contrib{tok, ms}, rest} : Wr.Dec<Cc.Contrib>}
      {==}

# a spelled list of Cc.Contrib whose count and items fit reads back
def cct.cl.go_rt(+t: List<&2, Cc.Contrib>, +x: Cc.Contrib, +rest: String, +h: {CompactionCut.contribs_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Cc.Contrib, ~FCc.get_contrib, List.length(&2, Cc.Contrib, t), FCc.get_contrib(CompactionCut.spell_contrib(x, CompactionCut.spell_contribs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cc.Contrib>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Cc.Contrib>, FCc.get_contrib(CompactionCut.spell_contrib(x, rest)), Wr.Got{x, rest}, cct.contrib(x, rest, LACo.co.and_l(CompactionCut.contrib_fits(x), CompactionCut.contribs_all([]), h))) : {Wr.get_list.go(~Cc.Contrib, ~FCc.get_contrib, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Cc.Contrib>>}
      {==}
    case Con{+y, +u}:
      +r2 = CompactionCut.spell_contrib(y, CompactionCut.spell_contribs.items(u, rest))
      %Equal.sym(Wr.Dec<Cc.Contrib>, FCc.get_contrib(CompactionCut.spell_contrib(x, r2)), Wr.Got{x, r2}, cct.contrib(x, r2, LACo.co.and_l(CompactionCut.contrib_fits(x), CompactionCut.contribs_all(y <> u), h))) : {Wr.get_list.go(~Cc.Contrib, ~FCc.get_contrib, 1n+List.length(&2, Cc.Contrib, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cc.Contrib>>}
      %Equal.sym(Wr.Dec<List<&2, Cc.Contrib>>, Wr.get_list.go(~Cc.Contrib, ~FCc.get_contrib, List.length(&2, Cc.Contrib, u), FCc.get_contrib(r2)), Wr.Got{y <> u, rest}, cct.cl.go_rt(u, y, rest, LACo.co.and_r(CompactionCut.contrib_fits(x), CompactionCut.contribs_all(y <> u), h))) : {Wr.get_list.cons(Cc.Contrib, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cc.Contrib>>}
      {==}

def cct.cl.rt(+xs: List<&2, Cc.Contrib>, +r: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, Cc.Contrib, xs)), CompactionCut.contribs_all(xs)) == True{} : Bool}) -> {Wr.get_list(~Cc.Contrib, ~FCc.get_contrib, Wr.put_nat(List.length(&2, Cc.Contrib, xs), CompactionCut.spell_contribs.items(xs, r))) == Wr.Got{xs, r} : Wr.Dec<List<&2, Cc.Contrib>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, r)), Wr.Got{0n, r}, Wire.wire_nat_round_trip(0n, r, {==})) : {Wr.get_list.start(~Cc.Contrib, ~FCc.get_contrib, _) == Wr.Got{Nil{}, r} : Wr.Dec<List<&2, Cc.Contrib>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Cc.Contrib, x <> t), CompactionCut.spell_contribs.items(x <> t, r))), Wr.Got{List.length(&2, Cc.Contrib, x <> t), CompactionCut.spell_contribs.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Cc.Contrib, x <> t), CompactionCut.spell_contribs.items(x <> t, r), LACo.co.and_l(LawsBase.wire_fits(List.length(&2, Cc.Contrib, x <> t)), CompactionCut.contribs_all(x <> t), h))) : {Wr.get_list.start(~Cc.Contrib, ~FCc.get_contrib, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Cc.Contrib>>}
      cct.cl.go_rt(t, x, r, LACo.co.and_r(LawsBase.wire_fits(List.length(&2, Cc.Contrib, x <> t)), CompactionCut.contribs_all(x <> t), h))

def cct.err(m: Maybe<&2, String>, +rest: String, +h: {CompactionCut.err_fits(m) == True{} : Bool}) -> {FCc.get_err(CompactionCut.spell_err(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      %LACoRead.cot.nat(0n, rest, {==}) : {FCc.get_err.tag(_) == Wr.Got{None{}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}
    case Some{+e}:
      %LACoRead.cot.nat(1n, Wr.put_str(e, rest), {==}) : {FCc.get_err.tag(_) == Wr.Got{Some{e}, rest} : Wr.Dec<Maybe<&2, String>>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(e, rest)), Wr.Got{e, rest}, Wire.wire_str_round_trip(e, rest, h)) : {FCc.get_err.text(_) == Wr.Got{Some{e}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

# a spelled request whose numbers fit reads back
def cct.req(q: FCc.Req, +rest: String, +h: {CompactionCut.req_fits(q) == True{} : Bool}) -> {FCc.get_req(CompactionCut.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FCc.Req>}:
  match q:
    case FCc.QCut{+hd, +l, +cs}:
      +r2 = Wr.put_nat(List.length(&2, Cc.Contrib, cs), CompactionCut.spell_contribs.items(cs, rest))
      +x = Bool.and(LawsBase.wire_fits(List.length(&2, Cc.Contrib, cs)), CompactionCut.contribs_all(cs))
      %LACoRead.cot.nat(0n, Wr.put_bool(hd, CompactionCut.spell_limit(l, r2)), {==}) : {FCc.get_req.tag(_) == Wr.Got{FCc.QCut{hd, l, cs}, rest} : Wr.Dec<FCc.Req>}
      %LACoRead.cot.bool(hd, CompactionCut.spell_limit(l, r2)) : {FCc.get_cut(_) == Wr.Got{FCc.QCut{hd, l, cs}, rest} : Wr.Dec<FCc.Req>}
      %Equal.sym(Wr.Dec<Cc.Limit>, FCc.get_limit(CompactionCut.spell_limit(l, r2)), Wr.Got{l, r2}, cct.limit(l, r2, LACo.co.and_l(CompactionCut.limit_fits(l), x, h))) : {FCc.get_cut.lim(hd, _) == Wr.Got{FCc.QCut{hd, l, cs}, rest} : Wr.Dec<FCc.Req>}
      %Equal.sym(Wr.Dec<List<&2, Cc.Contrib>>, Wr.get_list(~Cc.Contrib, ~FCc.get_contrib, r2), Wr.Got{cs, rest}, cct.cl.rt(cs, rest, LACo.co.and_r(CompactionCut.limit_fits(l), x, h))) : {FCc.get_cut.cs(hd, l, _) == Wr.Got{FCc.QCut{hd, l, cs}, rest} : Wr.Dec<FCc.Req>}
      {==}
    case FCc.QSummary{+s, +c, +x, +e}:
      +r3 = CompactionCut.spell_err(e, rest)
      %LACoRead.cot.nat(1n, ContextOrder.spell_stop(s, Wr.put_bool(c, Wr.put_bool(x, r3))), {==}) : {FCc.get_req.tag(_) == Wr.Got{FCc.QSummary{s, c, x, e}, rest} : Wr.Dec<FCc.Req>}
      %Equal.sym(Wr.Dec<Co.Stop>, FCo.get_stop(ContextOrder.spell_stop(s, Wr.put_bool(c, Wr.put_bool(x, r3)))), Wr.Got{s, Wr.put_bool(c, Wr.put_bool(x, r3))}, LACoRead.cot.stop(s, Wr.put_bool(c, Wr.put_bool(x, r3)))) : {FCc.get_summary(_) == Wr.Got{FCc.QSummary{s, c, x, e}, rest} : Wr.Dec<FCc.Req>}
      %LACoRead.cot.bool(c, Wr.put_bool(x, r3)) : {FCc.get_summary.calls(s, _) == Wr.Got{FCc.QSummary{s, c, x, e}, rest} : Wr.Dec<FCc.Req>}
      %LACoRead.cot.bool(x, r3) : {FCc.get_summary.text(s, c, _) == Wr.Got{FCc.QSummary{s, c, x, e}, rest} : Wr.Dec<FCc.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FCc.get_err(r3), Wr.Got{e, rest}, cct.err(e, rest, h)) : {FCc.get_summary.err(s, c, x, _) == Wr.Got{FCc.QSummary{s, c, x, e}, rest} : Wr.Dec<FCc.Req>}
      {==}
