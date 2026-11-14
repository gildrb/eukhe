# eukhe: lemmas of the entry proofs of area verify: a spelled request that
# fits the wire reads back with the rest untouched (ve.nat to ve.req:
# wire_nat_round_trip for the numbers, a round trip of the slots written
# here), and the entry's reply encoders are the spec spellers (ve.put_*,
# ve.acted, ve.advanced, ve.answer)

import Base
import ../../../bend/verify.bend as V
import ../../../bend/ffi_verify.bend as FV
import ../../../bend/wire.bend as Wr
import ../../../spec/verified/verify_wire.bend as SW
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../base/wire.bend as LWire

# Bool
# ----

def ve.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ve.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ve.BD(_, A, Unit)
  Unit{}

def ve.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ve.absurd({False{} == True{} : Bool}, h)

def ve.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ve.absurd({b == True{} : Bool}, h)

# Round trips: the value, then the rest, reads back from its spelling
# -------------------------------------------------------------------

def ve.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def ve.bool(b: Bool, rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ve.verdict(v: V.Verdict, rest: String) -> {Wr.Got{v, rest} == FV.get_verdict(Wr.get_nat(Wr.put_nat(SW.w_verdict(v), rest))) : Wr.Dec<V.Verdict>}:
  match v:
    case V.Confirmed{}:
      {==}
    case V.Refuted{}:
      {==}
    case V.Broken{}:
      {==}
    case V.Unjudged{}:
      {==}

def ve.actor(who: V.Actor, rest: String) -> {Wr.Got{who, rest} == FV.get_actor(Wr.get_nat(Wr.put_nat(SW.w_actor(who), rest))) : Wr.Dec<V.Actor>}:
  match who:
    case V.Owner{}:
      {==}
    case V.Worker{}:
      {==}
    case V.Verifier{}:
      {==}

def ve.ans(ans: V.Answer, rest: String) -> {Wr.Got{ans, rest} == FV.get_answer(Wr.get_nat(Wr.put_nat(SW.w_answer(ans), rest))) : Wr.Dec<V.Answer>}:
  match ans:
    case V.Yes{}:
      {==}
    case V.No{}:
      {==}
    case V.Unreadable{}:
      {==}
    case V.Unavailable{}:
      {==}
    case V.Stopped{}:
      {==}

def ve.evidence(ev: V.Evidence, +rest: String, h: {SW.fit_evidence(ev) == True{} : Bool}) -> {Wr.Got{ev, rest} == FV.get_evidence(Wr.get_nat(SW.w_evidence(ev, rest))) : Wr.Dec<V.Evidence>}:
  match ev:
    case V.Exited{+code}:
      %ve.nat(code, rest, h) : {Wr.Got{V.Exited{code}, rest} == FV.get_evidence.code(_) : Wr.Dec<V.Evidence>}
      {==}
    case V.NoStatus{}:
      {==}
    case V.TimedOut{}:
      {==}
    case V.SpawnFailed{}:
      {==}
    case V.Cancelled{}:
      {==}

def ve.op(op: V.Op, +rest: String, h: {SW.fit_op(op) == True{} : Bool}) -> {Wr.Got{op, rest} == FV.get_op(Wr.get_nat(SW.w_op(op, rest))) : Wr.Dec<V.Op>}:
  match op:
    case V.Assign{+n}:
      %ve.nat(n, rest, h) : {Wr.Got{V.Assign{n}, rest} == FV.get_op.assign(_) : Wr.Dec<V.Op>}
      {==}
    case V.Claim{}:
      {==}
    case V.Record{+rv, +i, +v, +at}:
      +hq = h
      +hr = ve.and_l(LawsBase.wire_fits(rv), Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(at)), hq)
      +h2 = ve.and_r(LawsBase.wire_fits(rv), Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(at)), hq)
      +hi = ve.and_l(LawsBase.wire_fits(i), LawsBase.wire_fits(at), h2)
      +ha = ve.and_r(LawsBase.wire_fits(i), LawsBase.wire_fits(at), h2)
      %ve.nat(rv, Wr.put_nat(i, Wr.put_nat(SW.w_verdict(v), Wr.put_nat(at, rest))), hr) : {Wr.Got{V.Record{rv, i, v, at}, rest} == FV.get_op.rev(_) : Wr.Dec<V.Op>}
      %ve.nat(i, Wr.put_nat(SW.w_verdict(v), Wr.put_nat(at, rest)), hi) : {Wr.Got{V.Record{rv, i, v, at}, rest} == FV.get_op.index(rv, _) : Wr.Dec<V.Op>}
      %ve.verdict(v, Wr.put_nat(at, rest)) : {Wr.Got{V.Record{rv, i, v, at}, rest} == FV.get_op.verdict(rv, i, _) : Wr.Dec<V.Op>}
      %ve.nat(at, rest, ha) : {Wr.Got{V.Record{rv, i, v, at}, rest} == FV.get_op.at(rv, i, v, _) : Wr.Dec<V.Op>}
      {==}

# Slots
# -----

# a spelled slot whose state fits reads back
def ve.slot(x: V.Slot, +rest: String, h: {SW.fit_slot(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FV.get_slot(SW.w_slot(x, rest)) : Wr.Dec<V.Slot>}:
  match x:
    case V.Open{}:
      {==}
    case V.Judged{+v, +at}:
      %ve.verdict(v, Wr.put_nat(at, rest)) : {Wr.Got{V.Judged{v, at}, rest} == FV.get_slot.verdict(_) : Wr.Dec<V.Slot>}
      %ve.nat(at, rest, h) : {Wr.Got{V.Judged{v, at}, rest} == FV.get_slot.at(v, _) : Wr.Dec<V.Slot>}
      {==}

# the items of a list of slots, then rest
def ve.items(xs: List<&2, V.Slot>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      SW.w_slot(x, ve.items(t, rest))

def ve.w_go(xs: List<&2, V.Slot>, -rest: String) -> {Wr.put_list.go(~V.Slot, ~SW.w_slot, xs, rest) == (List.length(&2, V.Slot, xs), ve.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~V.Slot, ~SW.w_slot, t, rest), (List.length(&2, V.Slot, t), ve.items(t, rest)), ve.w_go(t, rest)) : {Wr.put_list.step(~V.Slot, ~SW.w_slot, x, _) == (1n+List.length(&2, V.Slot, t), SW.w_slot(x, ve.items(t, rest))) : Nat & String}
      {==}

# the spelled slots are their count, then the items
def ve.w_slots(+xs: List<&2, V.Slot>, -rest: String) -> {SW.w_slots(xs, rest) == Wr.put_nat(List.length(&2, V.Slot, xs), ve.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~V.Slot, ~SW.w_slot, xs, rest), (List.length(&2, V.Slot, xs), ve.items(xs, rest)), ve.w_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, V.Slot, xs), ve.items(xs, rest)) : String}
  {==}

# the item loop reads back x, then t
def ve.go_rt(+t: List<&2, V.Slot>, +x: V.Slot, +rest: String, hx: {SW.fit_slot(x) == True{} : Bool}, ht: {SW.fit_slots.items(t) == True{} : Bool}) -> {Wr.get_list.go(~V.Slot, ~FV.get_slot, List.length(&2, V.Slot, t), FV.get_slot(SW.w_slot(x, ve.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, V.Slot>>}:
  match t:
    case Nil{}:
      %ve.slot(x, rest, hx) : {Wr.get_list.go(~V.Slot, ~FV.get_slot, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, V.Slot>>}
      {==}
    case +y <> +u:
      +hq = ht
      +hy = ve.and_l(SW.fit_slot(y), SW.fit_slots.items(u), hq)
      +hu = ve.and_r(SW.fit_slot(y), SW.fit_slots.items(u), hq)
      +r2 = SW.w_slot(y, ve.items(u, rest))
      %ve.slot(x, r2, hx) : {Wr.get_list.go(~V.Slot, ~FV.get_slot, 1n+List.length(&2, V.Slot, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, V.Slot>>}
      %Equal.sym(Wr.Dec<List<&2, V.Slot>>, Wr.get_list.go(~V.Slot, ~FV.get_slot, List.length(&2, V.Slot, u), FV.get_slot(r2)), Wr.Got{y <> u, rest}, ve.go_rt(u, y, rest, hy, hu)) : {Wr.get_list.cons(V.Slot, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, V.Slot>>}
      {==}

# the slots, their count and every state within the wire, read back
def ve.slots(xs: List<&2, V.Slot>, +rest: String, h: {SW.fit_slots(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == FV.get_slots(SW.w_slots(xs, rest)) : Wr.Dec<List<&2, V.Slot>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +hq = h
      +hn = ve.and_l(LawsBase.wire_fits(1n+List.length(&2, V.Slot, t)), SW.fit_slots.items(x <> t), hq)
      +hi = ve.and_r(LawsBase.wire_fits(1n+List.length(&2, V.Slot, t)), SW.fit_slots.items(x <> t), hq)
      +hx = ve.and_l(SW.fit_slot(x), SW.fit_slots.items(t), hi)
      +ht = ve.and_r(SW.fit_slot(x), SW.fit_slots.items(t), hi)
      %Equal.sym(String, SW.w_slots(x <> t, rest), Wr.put_nat(1n+List.length(&2, V.Slot, t), ve.items(x <> t, rest)), ve.w_slots(x <> t, rest)) : {Wr.Got{x <> t, rest} == Wr.get_list(~V.Slot, ~FV.get_slot, _) : Wr.Dec<List<&2, V.Slot>>}
      %ve.nat(1n+List.length(&2, V.Slot, t), ve.items(x <> t, rest), hn) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~V.Slot, ~FV.get_slot, _) : Wr.Dec<List<&2, V.Slot>>}
      Equal.sym(Wr.Dec<List<&2, V.Slot>>, Wr.get_list.go(~V.Slot, ~FV.get_slot, List.length(&2, V.Slot, t), FV.get_slot(SW.w_slot(x, ve.items(t, rest)))), Wr.Got{x <> t, rest}, ve.go_rt(t, x, rest, hx, ht))

# Acceptances
# -----------

def ve.acc(a: V.Acc, +rest: String, h: {SW.fit_acc(a) == True{} : Bool}) -> {Wr.Got{a, rest} == FV.get_acc(SW.w_acc(a, rest)) : Wr.Dec<V.Acc>}:
  match a:
    case V.Acc{+rev, +slots, +claimed, +tries}:
      +hq = h
      +hr = ve.and_l(LawsBase.wire_fits(rev), Bool.and(SW.fit_slots(slots), LawsBase.wire_fits(tries)), hq)
      +h2 = ve.and_r(LawsBase.wire_fits(rev), Bool.and(SW.fit_slots(slots), LawsBase.wire_fits(tries)), hq)
      +hs = ve.and_l(SW.fit_slots(slots), LawsBase.wire_fits(tries), h2)
      +ht = ve.and_r(SW.fit_slots(slots), LawsBase.wire_fits(tries), h2)
      +r1 = Wr.put_bool(claimed, Wr.put_nat(tries, rest))
      %ve.nat(rev, SW.w_slots(slots, r1), hr) : {Wr.Got{V.Acc{rev, slots, claimed, tries}, rest} == FV.get_acc.rev(_) : Wr.Dec<V.Acc>}
      %ve.slots(slots, r1, hs) : {Wr.Got{V.Acc{rev, slots, claimed, tries}, rest} == FV.get_acc.slots(rev, _) : Wr.Dec<V.Acc>}
      %ve.bool(claimed, Wr.put_nat(tries, rest)) : {Wr.Got{V.Acc{rev, slots, claimed, tries}, rest} == FV.get_acc.claimed(rev, slots, _) : Wr.Dec<V.Acc>}
      %ve.nat(tries, rest, ht) : {Wr.Got{V.Acc{rev, slots, claimed, tries}, rest} == FV.get_acc.tries(rev, slots, claimed, _) : Wr.Dec<V.Acc>}
      {==}

# Requests
# --------

# a spelled request that fits reads back, and the rest is untouched
def ve.req(q: FV.Req, +rest: String, h: {SW.fit_req(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FV.get_req(Wr.get_nat(SW.w_req(q, rest))) : Wr.Dec<FV.Req>}:
  match q:
    case FV.QAct{+who, +op, +a}:
      +hq = h
      +ho = ve.and_l(SW.fit_op(op), SW.fit_acc(a), hq)
      +ha = ve.and_r(SW.fit_op(op), SW.fit_acc(a), hq)
      %ve.actor(who, SW.w_op(op, SW.w_acc(a, rest))) : {Wr.Got{FV.QAct{who, op, a}, rest} == FV.get_req.act(_) : Wr.Dec<FV.Req>}
      %ve.op(op, SW.w_acc(a, rest), ho) : {Wr.Got{FV.QAct{who, op, a}, rest} == FV.get_req.act_op(who, _) : Wr.Dec<FV.Req>}
      %ve.acc(a, rest, ha) : {Wr.Got{FV.QAct{who, op, a}, rest} == FV.get_req.act_a(who, op, _) : Wr.Dec<FV.Req>}
      {==}
    case FV.QAdvance{+now, +cap, +a}:
      +hq = h
      +hn = ve.and_l(LawsBase.wire_fits(now), Bool.and(LawsBase.wire_fits(cap), SW.fit_acc(a)), hq)
      +h2 = ve.and_r(LawsBase.wire_fits(now), Bool.and(LawsBase.wire_fits(cap), SW.fit_acc(a)), hq)
      +hc = ve.and_l(LawsBase.wire_fits(cap), SW.fit_acc(a), h2)
      +ha = ve.and_r(LawsBase.wire_fits(cap), SW.fit_acc(a), h2)
      %ve.nat(now, Wr.put_nat(cap, SW.w_acc(a, rest)), hn) : {Wr.Got{FV.QAdvance{now, cap, a}, rest} == FV.get_req.advance(_) : Wr.Dec<FV.Req>}
      %ve.nat(cap, SW.w_acc(a, rest), hc) : {Wr.Got{FV.QAdvance{now, cap, a}, rest} == FV.get_req.advance_cap(now, _) : Wr.Dec<FV.Req>}
      %ve.acc(a, rest, ha) : {Wr.Got{FV.QAdvance{now, cap, a}, rest} == FV.get_req.advance_a(now, cap, _) : Wr.Dec<FV.Req>}
      {==}
    case FV.QLabel{+now, +slots}:
      +hq = h
      +hn = ve.and_l(LawsBase.wire_fits(now), SW.fit_slots(slots), hq)
      +hs = ve.and_r(LawsBase.wire_fits(now), SW.fit_slots(slots), hq)
      %ve.nat(now, SW.w_slots(slots, rest), hn) : {Wr.Got{FV.QLabel{now, slots}, rest} == FV.get_req.label(_) : Wr.Dec<FV.Req>}
      %ve.slots(slots, rest, hs) : {Wr.Got{FV.QLabel{now, slots}, rest} == FV.get_req.label_s(now, _) : Wr.Dec<FV.Req>}
      {==}
    case FV.QExit{+base, +now, +slots}:
      +hq = h
      +hb = ve.and_l(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), SW.fit_slots(slots)), hq)
      +h2 = ve.and_r(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), SW.fit_slots(slots)), hq)
      +hn = ve.and_l(LawsBase.wire_fits(now), SW.fit_slots(slots), h2)
      +hs = ve.and_r(LawsBase.wire_fits(now), SW.fit_slots(slots), h2)
      %ve.nat(base, Wr.put_nat(now, SW.w_slots(slots, rest)), hb) : {Wr.Got{FV.QExit{base, now, slots}, rest} == FV.get_req.exit(_) : Wr.Dec<FV.Req>}
      %ve.nat(now, SW.w_slots(slots, rest), hn) : {Wr.Got{FV.QExit{base, now, slots}, rest} == FV.get_req.exit_now(base, _) : Wr.Dec<FV.Req>}
      %ve.slots(slots, rest, hs) : {Wr.Got{FV.QExit{base, now, slots}, rest} == FV.get_req.exit_s(base, now, _) : Wr.Dec<FV.Req>}
      {==}
    case FV.QCommand{+expect, +intact, +ev}:
      +hq = h
      +he = ve.and_l(LawsBase.wire_fits(expect), SW.fit_evidence(ev), hq)
      +hv = ve.and_r(LawsBase.wire_fits(expect), SW.fit_evidence(ev), hq)
      %ve.nat(expect, Wr.put_bool(intact, SW.w_evidence(ev, rest)), he) : {Wr.Got{FV.QCommand{expect, intact, ev}, rest} == FV.get_req.command(_) : Wr.Dec<FV.Req>}
      %ve.bool(intact, SW.w_evidence(ev, rest)) : {Wr.Got{FV.QCommand{expect, intact, ev}, rest} == FV.get_req.command_intact(expect, _) : Wr.Dec<FV.Req>}
      %ve.evidence(ev, rest, hv) : {Wr.Got{FV.QCommand{expect, intact, ev}, rest} == FV.get_req.command_ev(expect, intact, _) : Wr.Dec<FV.Req>}
      {==}
    case FV.QUntil{+ev}:
      %ve.evidence(ev, rest, h) : {Wr.Got{FV.QUntil{ev}, rest} == FV.get_req.until(_) : Wr.Dec<FV.Req>}
      {==}
    case FV.QJudge{+ans}:
      %ve.ans(ans, rest) : {Wr.Got{FV.QJudge{ans}, rest} == FV.get_req.judge(_) : Wr.Dec<FV.Req>}
      {==}
    case FV.QClaims{+held, +checked, +goal, +claimed, +ended}:
      %ve.bool(held, Wr.put_bool(checked, Wr.put_bool(goal, Wr.put_bool(claimed, Wr.put_bool(ended, rest))))) : {Wr.Got{FV.QClaims{held, checked, goal, claimed, ended}, rest} == FV.get_req.claims(_) : Wr.Dec<FV.Req>}
      %ve.bool(checked, Wr.put_bool(goal, Wr.put_bool(claimed, Wr.put_bool(ended, rest)))) : {Wr.Got{FV.QClaims{held, checked, goal, claimed, ended}, rest} == FV.get_req.claims_k(held, _) : Wr.Dec<FV.Req>}
      %ve.bool(goal, Wr.put_bool(claimed, Wr.put_bool(ended, rest))) : {Wr.Got{FV.QClaims{held, checked, goal, claimed, ended}, rest} == FV.get_req.claims_g(held, checked, _) : Wr.Dec<FV.Req>}
      %ve.bool(claimed, Wr.put_bool(ended, rest)) : {Wr.Got{FV.QClaims{held, checked, goal, claimed, ended}, rest} == FV.get_req.claims_c(held, checked, goal, _) : Wr.Dec<FV.Req>}
      %ve.bool(ended, rest) : {Wr.Got{FV.QClaims{held, checked, goal, claimed, ended}, rest} == FV.get_req.claims_e(held, checked, goal, claimed, _) : Wr.Dec<FV.Req>}
      {==}

# Replies: the encoders are the spec spellers
# ------------------------------------------

def ve.put_verdict(v: V.Verdict, rest: String) -> {FV.put_verdict(v, rest) == Wr.put_nat(SW.w_verdict(v), rest) : String}:
  match v:
    case V.Confirmed{}:
      {==}
    case V.Refuted{}:
      {==}
    case V.Broken{}:
      {==}
    case V.Unjudged{}:
      {==}

def ve.put_label(l: V.Label, rest: String) -> {FV.put_label(l, rest) == Wr.put_nat(SW.w_label(l), rest) : String}:
  match l:
    case V.Verified{}:
      {==}
    case V.Failed{}:
      {==}
    case V.Unverified{}:
      {==}
    case V.Passed{}:
      {==}

def ve.put_slot(x: V.Slot, rest: String) -> {FV.put_slot(x, rest) == SW.w_slot(x, rest) : String}:
  match x:
    case V.Open{}:
      {==}
    case V.Judged{v, at}:
      match v:
        case V.Confirmed{}:
          {==}
        case V.Refuted{}:
          {==}
        case V.Broken{}:
          {==}
        case V.Unjudged{}:
          {==}

def ve.put_step(x: V.Slot, g: Nat & String) -> {Wr.put_list.step(~V.Slot, ~FV.put_slot, x, g) == Wr.put_list.step(~V.Slot, ~SW.w_slot, x, g) : Nat & String}:
  (n, +s) = g
  %ve.put_slot(x, s) : {(1n+n, FV.put_slot(x, s)) == (1n+n, _) : Nat & String}
  {==}

def ve.put_go(xs: List<&2, V.Slot>, +rest: String) -> {Wr.put_list.go(~V.Slot, ~FV.put_slot, xs, rest) == Wr.put_list.go(~V.Slot, ~SW.w_slot, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %ve.put_go(t, rest) : {Wr.put_list.step(~V.Slot, ~FV.put_slot, x, Wr.put_list.go(~V.Slot, ~FV.put_slot, t, rest)) == Wr.put_list.step(~V.Slot, ~SW.w_slot, x, _) : Nat & String}
      ve.put_step(x, Wr.put_list.go(~V.Slot, ~FV.put_slot, t, rest))

def ve.put_acc(a: V.Acc, +rest: String) -> {FV.put_acc(a, rest) == SW.w_acc(a, rest) : String}:
  match a:
    case V.Acc{+rev, +slots, +claimed, +tries}:
      +r1 = Wr.put_bool(claimed, Wr.put_nat(tries, rest))
      %ve.put_go(slots, r1) : {Wr.put_nat(rev, Wr.put_list.fin(Wr.put_list.go(~V.Slot, ~FV.put_slot, slots, r1))) == Wr.put_nat(rev, Wr.put_list.fin(_)) : String}
      {==}

def ve.put_action(x: V.Action, rest: String) -> {FV.put_action(x, rest) == SW.w_action(x, rest) : String}:
  match x:
    case V.Rest{}:
      {==}
    case V.Run{i}:
      {==}
    case V.Return{}:
      {==}
    case V.End{l}:
      match l:
        case V.Verified{}:
          {==}
        case V.Failed{}:
          {==}
        case V.Unverified{}:
          {==}
        case V.Passed{}:
          {==}

def ve.acted(r: Bool & V.Acc) -> {FV.put_acted(r) == SW.w_acted(r) : String}:
  (+ok, +a) = r
  %ve.put_acc(a, "") : {Wr.put_bool(ok, FV.put_acc(a, "")) == Wr.put_bool(ok, _) : String}
  {==}

def ve.advanced(r: V.Action & V.Acc) -> {FV.put_advanced(r) == SW.w_advanced(r) : String}:
  (+x, +a) = r
  %ve.put_acc(a, "") : {FV.put_action(x, FV.put_acc(a, "")) == SW.w_action(x, _) : String}
  ve.put_action(x, FV.put_acc(a, ""))

# the reply of a request is the spec's spelling of the model's decision
def ve.answer(q: FV.Req) -> {FV.answer(q) == SW.w_reply(q) : String}:
  match q:
    case FV.QAct{who, op, a}:
      ve.acted(V.act(who, op, a))
    case FV.QAdvance{now, cap, a}:
      ve.advanced(V.advance(False{}, now, cap, a))
    case FV.QLabel{now, slots}:
      ve.put_label(V.label(False{}, now, slots), "")
    case FV.QExit{base, now, slots}:
      {==}
    case FV.QCommand{expect, intact, ev}:
      ve.put_verdict(V.grade_command(expect, intact, ev), "")
    case FV.QUntil{ev}:
      ve.put_verdict(V.grade_until(ev), "")
    case FV.QJudge{ans}:
      ve.put_verdict(V.grade_judge(ans), "")
    case FV.QClaims{held, checked, goal, claimed, ended}:
      {==}
