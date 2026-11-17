# eukhe: lemmas of the entry proofs of area strength: a spelled request
# that fits the wire reads back with the rest untouched (se.vlabel to
# se.req: the numbers by wire_nat_round_trip through LE.ve.nat, the slots
# and the actor as the verify entry reads them, a round trip of the
# gauges written here), and the entry's reply encoders are the spec
# spellers (se.put_*, se.recorded, se.answer)

import Base
import ../../../bend/verify.bend as V
import ../../../bend/strength.bend as St
import ../../../bend/ffi_strength.bend as FS
import ../../../bend/ffi_verify.bend as FV
import ../../../bend/wire.bend as Wr
import ../../../spec/verified/verify_wire.bend as SVW
import ../../../spec/verified/strength_wire.bend as SW
import ../../../laws/base.bend as LawsBase
import ../../verify/base/entry.bend as LE

# Round trips: the value, then the rest, reads back from its spelling
# -------------------------------------------------------------------

def se.vlabel(l: V.Label, rest: String) -> {Wr.Got{l, rest} == FS.get_vlabel(Wr.get_nat(Wr.put_nat(SW.w_vlabel(l), rest))) : Wr.Dec<V.Label>}:
  match l:
    case V.Verified{}:
      {==}
    case V.Failed{}:
      {==}
    case V.Unverified{}:
      {==}
    case V.Passed{}:
      {==}

def se.bar(b: St.Bar, +rest: String, h: {SW.fit_bar(b) == True{} : Bool}) -> {Wr.Got{b, rest} == FS.get_bar(Wr.get_nat(SW.w_bar(b, rest))) : Wr.Dec<St.Bar>}:
  match b:
    case St.Exempt{}:
      {==}
    case St.Waived{}:
      {==}
    case St.Needs{+pct}:
      %LE.ve.nat(pct, rest, h) : {Wr.Got{St.Needs{pct}, rest} == FS.get_bar.pct(_) : Wr.Dec<St.Bar>}
      {==}

def se.mark(m: St.Mark, +rest: String, h: {SW.fit_mark(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FS.get_mark(Wr.get_nat(SW.w_mark(m, rest))) : Wr.Dec<St.Mark>}:
  match m:
    case St.Unmeasured{}:
      {==}
    case St.Measured{+c, +n, +p, +at}:
      +hq = h
      +hc = LE.ve.and_l(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(at))), hq)
      +h2 = LE.ve.and_r(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(at))), hq)
      +hn = LE.ve.and_l(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(at)), h2)
      +h3 = LE.ve.and_r(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(at)), h2)
      +hp = LE.ve.and_l(LawsBase.wire_fits(p), LawsBase.wire_fits(at), h3)
      +ha = LE.ve.and_r(LawsBase.wire_fits(p), LawsBase.wire_fits(at), h3)
      %LE.ve.nat(c, Wr.put_nat(n, Wr.put_nat(p, Wr.put_nat(at, rest))), hc) : {Wr.Got{St.Measured{c, n, p, at}, rest} == FS.get_mark.caught(_) : Wr.Dec<St.Mark>}
      %LE.ve.nat(n, Wr.put_nat(p, Wr.put_nat(at, rest)), hn) : {Wr.Got{St.Measured{c, n, p, at}, rest} == FS.get_mark.ran(c, _) : Wr.Dec<St.Mark>}
      %LE.ve.nat(p, Wr.put_nat(at, rest), hp) : {Wr.Got{St.Measured{c, n, p, at}, rest} == FS.get_mark.planned(c, n, _) : Wr.Dec<St.Mark>}
      %LE.ve.nat(at, rest, ha) : {Wr.Got{St.Measured{c, n, p, at}, rest} == FS.get_mark.at(c, n, p, _) : Wr.Dec<St.Mark>}
      {==}

def se.gauge(g: St.Gauge, +rest: String, h: {SW.fit_gauge(g) == True{} : Bool}) -> {Wr.Got{g, rest} == FS.get_gauge(SW.w_gauge(g, rest)) : Wr.Dec<St.Gauge>}:
  match g:
    case St.Gauge{+b, +m}:
      +hq = h
      +hb = LE.ve.and_l(SW.fit_bar(b), SW.fit_mark(m), hq)
      +hm = LE.ve.and_r(SW.fit_bar(b), SW.fit_mark(m), hq)
      %se.bar(b, SW.w_mark(m, rest), hb) : {Wr.Got{St.Gauge{b, m}, rest} == FS.get_gauge.bar(_) : Wr.Dec<St.Gauge>}
      %se.mark(m, rest, hm) : {Wr.Got{St.Gauge{b, m}, rest} == FS.get_gauge.mark(b, _) : Wr.Dec<St.Gauge>}
      {==}

# Gauges
# ------

# the items of a list of gauges, then rest
def se.items(xs: List<&2, St.Gauge>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      SW.w_gauge(x, se.items(t, rest))

def se.w_go(xs: List<&2, St.Gauge>, -rest: String) -> {Wr.put_list.go(~St.Gauge, ~SW.w_gauge, xs, rest) == (List.length(&2, St.Gauge, xs), se.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~St.Gauge, ~SW.w_gauge, t, rest), (List.length(&2, St.Gauge, t), se.items(t, rest)), se.w_go(t, rest)) : {Wr.put_list.step(~St.Gauge, ~SW.w_gauge, x, _) == (1n+List.length(&2, St.Gauge, t), SW.w_gauge(x, se.items(t, rest))) : Nat & String}
      {==}

# the spelled gauges are their count, then the items
def se.w_gauges(+xs: List<&2, St.Gauge>, -rest: String) -> {SW.w_gauges(xs, rest) == Wr.put_nat(List.length(&2, St.Gauge, xs), se.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~St.Gauge, ~SW.w_gauge, xs, rest), (List.length(&2, St.Gauge, xs), se.items(xs, rest)), se.w_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, St.Gauge, xs), se.items(xs, rest)) : String}
  {==}

# the item loop reads back x, then t
def se.go_rt(+t: List<&2, St.Gauge>, +x: St.Gauge, +rest: String, hx: {SW.fit_gauge(x) == True{} : Bool}, ht: {SW.fit_gauges.items(t) == True{} : Bool}) -> {Wr.get_list.go(~St.Gauge, ~FS.get_gauge, List.length(&2, St.Gauge, t), FS.get_gauge(SW.w_gauge(x, se.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, St.Gauge>>}:
  match t:
    case Nil{}:
      %se.gauge(x, rest, hx) : {Wr.get_list.go(~St.Gauge, ~FS.get_gauge, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, St.Gauge>>}
      {==}
    case +y <> +u:
      +hq = ht
      +hy = LE.ve.and_l(SW.fit_gauge(y), SW.fit_gauges.items(u), hq)
      +hu = LE.ve.and_r(SW.fit_gauge(y), SW.fit_gauges.items(u), hq)
      +r2 = SW.w_gauge(y, se.items(u, rest))
      %se.gauge(x, r2, hx) : {Wr.get_list.go(~St.Gauge, ~FS.get_gauge, 1n+List.length(&2, St.Gauge, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, St.Gauge>>}
      %Equal.sym(Wr.Dec<List<&2, St.Gauge>>, Wr.get_list.go(~St.Gauge, ~FS.get_gauge, List.length(&2, St.Gauge, u), FS.get_gauge(r2)), Wr.Got{y <> u, rest}, se.go_rt(u, y, rest, hy, hu)) : {Wr.get_list.cons(St.Gauge, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, St.Gauge>>}
      {==}

# the gauges, their count and every number within the wire, read back
def se.gauges(xs: List<&2, St.Gauge>, +rest: String, h: {SW.fit_gauges(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == FS.get_gauges(SW.w_gauges(xs, rest)) : Wr.Dec<List<&2, St.Gauge>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +hq = h
      +hn = LE.ve.and_l(LawsBase.wire_fits(1n+List.length(&2, St.Gauge, t)), SW.fit_gauges.items(x <> t), hq)
      +hi = LE.ve.and_r(LawsBase.wire_fits(1n+List.length(&2, St.Gauge, t)), SW.fit_gauges.items(x <> t), hq)
      +hx = LE.ve.and_l(SW.fit_gauge(x), SW.fit_gauges.items(t), hi)
      +ht = LE.ve.and_r(SW.fit_gauge(x), SW.fit_gauges.items(t), hi)
      %Equal.sym(String, SW.w_gauges(x <> t, rest), Wr.put_nat(1n+List.length(&2, St.Gauge, t), se.items(x <> t, rest)), se.w_gauges(x <> t, rest)) : {Wr.Got{x <> t, rest} == Wr.get_list(~St.Gauge, ~FS.get_gauge, _) : Wr.Dec<List<&2, St.Gauge>>}
      %LE.ve.nat(1n+List.length(&2, St.Gauge, t), se.items(x <> t, rest), hn) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~St.Gauge, ~FS.get_gauge, _) : Wr.Dec<List<&2, St.Gauge>>}
      Equal.sym(Wr.Dec<List<&2, St.Gauge>>, Wr.get_list.go(~St.Gauge, ~FS.get_gauge, List.length(&2, St.Gauge, t), FS.get_gauge(SW.w_gauge(x, se.items(t, rest)))), Wr.Got{x <> t, rest}, se.go_rt(t, x, rest, hx, ht))

# Requests
# --------

# a spelled request that fits reads back, and the rest is untouched
def se.req(q: FS.Req, +rest: String, h: {SW.fit_req(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FS.get_req(Wr.get_nat(SW.w_req(q, rest))) : Wr.Dec<FS.Req>}:
  match q:
    case FS.QSettle{+l, +now, +gs}:
      +hq = h
      +hn = LE.ve.and_l(LawsBase.wire_fits(now), SW.fit_gauges(gs), hq)
      +hg = LE.ve.and_r(LawsBase.wire_fits(now), SW.fit_gauges(gs), hq)
      %se.vlabel(l, Wr.put_nat(now, SW.w_gauges(gs, rest))) : {Wr.Got{FS.QSettle{l, now, gs}, rest} == FS.get_req.settle(_) : Wr.Dec<FS.Req>}
      %LE.ve.nat(now, SW.w_gauges(gs, rest), hn) : {Wr.Got{FS.QSettle{l, now, gs}, rest} == FS.get_req.settle_now(l, _) : Wr.Dec<FS.Req>}
      %se.gauges(gs, rest, hg) : {Wr.Got{FS.QSettle{l, now, gs}, rest} == FS.get_req.settle_gs(l, now, _) : Wr.Dec<FS.Req>}
      {==}
    case FS.QLabel{+l, +now, +gs}:
      +hq = h
      +hn = LE.ve.and_l(LawsBase.wire_fits(now), SW.fit_gauges(gs), hq)
      +hg = LE.ve.and_r(LawsBase.wire_fits(now), SW.fit_gauges(gs), hq)
      %se.vlabel(l, Wr.put_nat(now, SW.w_gauges(gs, rest))) : {Wr.Got{FS.QLabel{l, now, gs}, rest} == FS.get_req.label(_) : Wr.Dec<FS.Req>}
      %LE.ve.nat(now, SW.w_gauges(gs, rest), hn) : {Wr.Got{FS.QLabel{l, now, gs}, rest} == FS.get_req.label_now(l, _) : Wr.Dec<FS.Req>}
      %se.gauges(gs, rest, hg) : {Wr.Got{FS.QLabel{l, now, gs}, rest} == FS.get_req.label_gs(l, now, _) : Wr.Dec<FS.Req>}
      {==}
    case FS.QExit{+base, +now, +slots, +gs}:
      +hq = h
      +hb = LE.ve.and_l(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), SW.fit_gauges(gs))), hq)
      +h2 = LE.ve.and_r(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), SW.fit_gauges(gs))), hq)
      +hn = LE.ve.and_l(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), SW.fit_gauges(gs)), h2)
      +h3 = LE.ve.and_r(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), SW.fit_gauges(gs)), h2)
      +hs = LE.ve.and_l(SVW.fit_slots(slots), SW.fit_gauges(gs), h3)
      +hg = LE.ve.and_r(SVW.fit_slots(slots), SW.fit_gauges(gs), h3)
      %LE.ve.nat(base, Wr.put_nat(now, SVW.w_slots(slots, SW.w_gauges(gs, rest))), hb) : {Wr.Got{FS.QExit{base, now, slots, gs}, rest} == FS.get_req.exit(_) : Wr.Dec<FS.Req>}
      %LE.ve.nat(now, SVW.w_slots(slots, SW.w_gauges(gs, rest)), hn) : {Wr.Got{FS.QExit{base, now, slots, gs}, rest} == FS.get_req.exit_now(base, _) : Wr.Dec<FS.Req>}
      %LE.ve.slots(slots, SW.w_gauges(gs, rest), hs) : {Wr.Got{FS.QExit{base, now, slots, gs}, rest} == FS.get_req.exit_slots(base, now, _) : Wr.Dec<FS.Req>}
      %se.gauges(gs, rest, hg) : {Wr.Got{FS.QExit{base, now, slots, gs}, rest} == FS.get_req.exit_gs(base, now, slots, _) : Wr.Dec<FS.Req>}
      {==}
    case FS.QRecord{+who, +i, +m, +gs}:
      +hq = h
      +hi = LE.ve.and_l(LawsBase.wire_fits(i), Bool.and(SW.fit_mark(m), SW.fit_gauges(gs)), hq)
      +h2 = LE.ve.and_r(LawsBase.wire_fits(i), Bool.and(SW.fit_mark(m), SW.fit_gauges(gs)), hq)
      +hm = LE.ve.and_l(SW.fit_mark(m), SW.fit_gauges(gs), h2)
      +hg = LE.ve.and_r(SW.fit_mark(m), SW.fit_gauges(gs), h2)
      %LE.ve.actor(who, Wr.put_nat(i, SW.w_mark(m, SW.w_gauges(gs, rest)))) : {Wr.Got{FS.QRecord{who, i, m, gs}, rest} == FS.get_req.record(_) : Wr.Dec<FS.Req>}
      %LE.ve.nat(i, SW.w_mark(m, SW.w_gauges(gs, rest)), hi) : {Wr.Got{FS.QRecord{who, i, m, gs}, rest} == FS.get_req.record_i(who, _) : Wr.Dec<FS.Req>}
      %se.mark(m, SW.w_gauges(gs, rest), hm) : {Wr.Got{FS.QRecord{who, i, m, gs}, rest} == FS.get_req.record_mark(who, i, _) : Wr.Dec<FS.Req>}
      %se.gauges(gs, rest, hg) : {Wr.Got{FS.QRecord{who, i, m, gs}, rest} == FS.get_req.record_gs(who, i, m, _) : Wr.Dec<FS.Req>}
      {==}
    case FS.QStrength{+now, +g}:
      +hq = h
      +hn = LE.ve.and_l(LawsBase.wire_fits(now), SW.fit_gauge(g), hq)
      +hg = LE.ve.and_r(LawsBase.wire_fits(now), SW.fit_gauge(g), hq)
      %LE.ve.nat(now, SW.w_gauge(g, rest), hn) : {Wr.Got{FS.QStrength{now, g}, rest} == FS.get_req.strength(_) : Wr.Dec<FS.Req>}
      %se.gauge(g, rest, hg) : {Wr.Got{FS.QStrength{now, g}, rest} == FS.get_req.strength_g(now, _) : Wr.Dec<FS.Req>}
      {==}

# Replies: the encoders are the spec spellers
# ------------------------------------------

def se.put_label(l: St.Label, rest: String) -> {FS.put_label(l, rest) == Wr.put_nat(SW.w_label(l), rest) : String}:
  match l:
    case St.Verified{}:
      {==}
    case St.Failed{}:
      {==}
    case St.Unverified{}:
      {==}
    case St.Passed{}:
      {==}
    case St.Uncertified{}:
      {==}

def se.put_step(x: St.Step) -> {FS.put_step(x, "") == SW.w_step(x) : String}:
  match x:
    case St.Measure{i}:
      {==}
    case St.End{l}:
      match l:
        case St.Verified{}:
          {==}
        case St.Failed{}:
          {==}
        case St.Unverified{}:
          {==}
        case St.Passed{}:
          {==}
        case St.Uncertified{}:
          {==}

def se.put_strength(x: St.Strength) -> {FS.put_strength(x, "") == Wr.put_nat(SW.w_strength(x), "") : String}:
  match x:
    case St.Strong{}:
      {==}
    case St.Weak{}:
      {==}
    case St.Unshown{}:
      {==}
    case St.Free{}:
      {==}

def se.put_gauge(g: St.Gauge, rest: String) -> {FS.put_gauge(g, rest) == SW.w_gauge(g, rest) : String}:
  match g:
    case St.Gauge{b, m}:
      match b:
        case St.Exempt{}:
          match m:
            case St.Unmeasured{}:
              {==}
            case St.Measured{c, n, p, at}:
              {==}
        case St.Waived{}:
          match m:
            case St.Unmeasured{}:
              {==}
            case St.Measured{c, n, p, at}:
              {==}
        case St.Needs{pct}:
          match m:
            case St.Unmeasured{}:
              {==}
            case St.Measured{c, n, p, at}:
              {==}

def se.pstep(x: St.Gauge, g: Nat & String) -> {Wr.put_list.step(~St.Gauge, ~FS.put_gauge, x, g) == Wr.put_list.step(~St.Gauge, ~SW.w_gauge, x, g) : Nat & String}:
  (n, +s) = g
  %se.put_gauge(x, s) : {(1n+n, FS.put_gauge(x, s)) == (1n+n, _) : Nat & String}
  {==}

def se.put_go(xs: List<&2, St.Gauge>, +rest: String) -> {Wr.put_list.go(~St.Gauge, ~FS.put_gauge, xs, rest) == Wr.put_list.go(~St.Gauge, ~SW.w_gauge, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %se.put_go(t, rest) : {Wr.put_list.step(~St.Gauge, ~FS.put_gauge, x, Wr.put_list.go(~St.Gauge, ~FS.put_gauge, t, rest)) == Wr.put_list.step(~St.Gauge, ~SW.w_gauge, x, _) : Nat & String}
      se.pstep(x, Wr.put_list.go(~St.Gauge, ~FS.put_gauge, t, rest))

def se.recorded(r: Bool & List<&2, St.Gauge>) -> {FS.put_recorded(r) == SW.w_recorded(r) : String}:
  (+ok, +gs) = r
  %se.put_go(gs, "") : {Wr.put_bool(ok, Wr.put_list.fin(Wr.put_list.go(~St.Gauge, ~FS.put_gauge, gs, ""))) == Wr.put_bool(ok, Wr.put_list.fin(_)) : String}
  {==}

# the reply of a request is the spec's spelling of the model's decision
def se.answer(q: FS.Req) -> {FS.answer(q) == SW.w_reply(q) : String}:
  match q:
    case FS.QSettle{l, now, gs}:
      se.put_step(St.settle(l, now, gs))
    case FS.QLabel{l, now, gs}:
      se.put_label(St.label(l, now, gs), "")
    case FS.QExit{base, now, slots, gs}:
      {==}
    case FS.QRecord{who, i, m, gs}:
      se.recorded(St.record(who, i, m, gs))
    case FS.QStrength{now, g}:
      se.put_strength(St.strength(now, g))
