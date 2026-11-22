# eukhe: lemmas of the entry proofs of area attack: a spelled request
# that fits the wire reads back with the rest untouched (ae.agrees to
# ae.req: the numbers by LVE.ve.nat, the Bools by LVE.ve.bool, the slots
# as the verify entry reads them, verify's label and the gauges as the
# strength entry reads them, a round trip of the outcomes written here),
# and the entry's reply encoders are the spec spellers (ae.put_outcome,
# ae.answer)

import Base
import ../../../bend/verify.bend as V
import ../../../bend/strength.bend as St
import ../../../bend/attack.bend as At
import ../../../bend/ffi_attack.bend as FA
import ../../../bend/wire.bend as Wr
import ../../../spec/verified/verify_wire.bend as SVW
import ../../../spec/verified/strength_wire.bend as SSW
import ../../../spec/verified/attack_wire.bend as SAW
import ../../../laws/base.bend as LawsBase
import ../../verify/base/entry.bend as LVE
import ../../strength/base/entry.bend as LSE

# Round trips: the value, then the rest, reads back from its spelling
# -------------------------------------------------------------------

def ae.agrees(m: Maybe<&2, Bool>, rest: String) -> {Wr.Got{m, rest} == FA.get_agrees(Wr.get_nat(SAW.w_agrees(m, rest))) : Wr.Dec<Maybe<&2, Bool>>}:
  match m:
    case None{}:
      {==}
    case Some{yes}:
      match yes:
        case True{}:
          {==}
        case False{}:
          {==}

def ae.outcome(o: At.Outcome, rest: String) -> {Wr.Got{o, rest} == FA.get_outcome(SAW.w_outcome_s(o, rest)) : Wr.Dec<At.Outcome>}:
  match o:
    case At.Survived{}:
      {==}
    case At.Clean{}:
      {==}
    case At.Unrun{}:
      {==}

# Outcomes
# --------

# the items of a list of outcomes, then rest
def ae.items(xs: List<&2, At.Outcome>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      SAW.w_outcome_s(x, ae.items(t, rest))

def ae.w_go(xs: List<&2, At.Outcome>, -rest: String) -> {Wr.put_list.go(~At.Outcome, ~SAW.w_outcome_s, xs, rest) == (List.length(&2, At.Outcome, xs), ae.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~At.Outcome, ~SAW.w_outcome_s, t, rest), (List.length(&2, At.Outcome, t), ae.items(t, rest)), ae.w_go(t, rest)) : {Wr.put_list.step(~At.Outcome, ~SAW.w_outcome_s, x, _) == (1n+List.length(&2, At.Outcome, t), SAW.w_outcome_s(x, ae.items(t, rest))) : Nat & String}
      {==}

# the spelled outcomes are their count, then the items
def ae.w_outcomes(+xs: List<&2, At.Outcome>, -rest: String) -> {SAW.w_outcomes(xs, rest) == Wr.put_nat(List.length(&2, At.Outcome, xs), ae.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~At.Outcome, ~SAW.w_outcome_s, xs, rest), (List.length(&2, At.Outcome, xs), ae.items(xs, rest)), ae.w_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, At.Outcome, xs), ae.items(xs, rest)) : String}
  {==}

# the item loop reads back x, then t
def ae.go_rt(+t: List<&2, At.Outcome>, +x: At.Outcome, +rest: String) -> {Wr.get_list.go(~At.Outcome, ~FA.get_outcome, List.length(&2, At.Outcome, t), FA.get_outcome(SAW.w_outcome_s(x, ae.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, At.Outcome>>}:
  match t:
    case Nil{}:
      %ae.outcome(x, rest) : {Wr.get_list.go(~At.Outcome, ~FA.get_outcome, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, At.Outcome>>}
      {==}
    case +y <> +u:
      +r2 = SAW.w_outcome_s(y, ae.items(u, rest))
      %ae.outcome(x, r2) : {Wr.get_list.go(~At.Outcome, ~FA.get_outcome, 1n+List.length(&2, At.Outcome, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, At.Outcome>>}
      %Equal.sym(Wr.Dec<List<&2, At.Outcome>>, Wr.get_list.go(~At.Outcome, ~FA.get_outcome, List.length(&2, At.Outcome, u), FA.get_outcome(r2)), Wr.Got{y <> u, rest}, ae.go_rt(u, y, rest)) : {Wr.get_list.cons(At.Outcome, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, At.Outcome>>}
      {==}

# the outcomes, their count within the wire, read back
def ae.outcomes(xs: List<&2, At.Outcome>, +rest: String, h: {SAW.fit_outcomes(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == FA.get_outcomes(SAW.w_outcomes(xs, rest)) : Wr.Dec<List<&2, At.Outcome>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(String, SAW.w_outcomes(x <> t, rest), Wr.put_nat(1n+List.length(&2, At.Outcome, t), ae.items(x <> t, rest)), ae.w_outcomes(x <> t, rest)) : {Wr.Got{x <> t, rest} == Wr.get_list(~At.Outcome, ~FA.get_outcome, _) : Wr.Dec<List<&2, At.Outcome>>}
      %LVE.ve.nat(1n+List.length(&2, At.Outcome, t), ae.items(x <> t, rest), h) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~At.Outcome, ~FA.get_outcome, _) : Wr.Dec<List<&2, At.Outcome>>}
      Equal.sym(Wr.Dec<List<&2, At.Outcome>>, Wr.get_list.go(~At.Outcome, ~FA.get_outcome, List.length(&2, At.Outcome, t), FA.get_outcome(SAW.w_outcome_s(x, ae.items(t, rest)))), Wr.Got{x <> t, rest}, ae.go_rt(t, x, rest))

# Requests
# --------

# a spelled request that fits reads back, and the rest is untouched
def ae.req(q: FA.Req, +rest: String, h: {SAW.fit_req(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FA.get_req(Wr.get_nat(SAW.w_req(q, rest))) : Wr.Dec<FA.Req>}:
  match q:
    case FA.QOutcome{r}:
      match r:
        case At.Run{+ran, +passes, +differs, +agrees}:
          %LVE.ve.bool(ran, Wr.put_bool(passes, Wr.put_bool(differs, SAW.w_agrees(agrees, rest)))) : {Wr.Got{FA.QOutcome{At.Run{ran, passes, differs, agrees}}, rest} == FA.get_req.outcome(_) : Wr.Dec<FA.Req>}
          %LVE.ve.bool(passes, Wr.put_bool(differs, SAW.w_agrees(agrees, rest))) : {Wr.Got{FA.QOutcome{At.Run{ran, passes, differs, agrees}}, rest} == FA.get_req.outcome_passes(ran, _) : Wr.Dec<FA.Req>}
          %LVE.ve.bool(differs, SAW.w_agrees(agrees, rest)) : {Wr.Got{FA.QOutcome{At.Run{ran, passes, differs, agrees}}, rest} == FA.get_req.outcome_differs(ran, passes, _) : Wr.Dec<FA.Req>}
          %ae.agrees(agrees, rest) : {Wr.Got{FA.QOutcome{At.Run{ran, passes, differs, agrees}}, rest} == FA.get_req.outcome_agrees(ran, passes, differs, _) : Wr.Dec<FA.Req>}
          {==}
    case FA.QLabel{+l, +now, +gs, +os}:
      +hq = h
      +hn = LVE.ve.and_l(LawsBase.wire_fits(now), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os)), hq)
      +h2 = LVE.ve.and_r(LawsBase.wire_fits(now), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os)), hq)
      +hg = LVE.ve.and_l(SSW.fit_gauges(gs), SAW.fit_outcomes(os), h2)
      +ho = LVE.ve.and_r(SSW.fit_gauges(gs), SAW.fit_outcomes(os), h2)
      %LSE.se.vlabel(l, Wr.put_nat(now, SSW.w_gauges(gs, SAW.w_outcomes(os, rest)))) : {Wr.Got{FA.QLabel{l, now, gs, os}, rest} == FA.get_req.label(_) : Wr.Dec<FA.Req>}
      %LVE.ve.nat(now, SSW.w_gauges(gs, SAW.w_outcomes(os, rest)), hn) : {Wr.Got{FA.QLabel{l, now, gs, os}, rest} == FA.get_req.label_now(l, _) : Wr.Dec<FA.Req>}
      %LSE.se.gauges(gs, SAW.w_outcomes(os, rest), hg) : {Wr.Got{FA.QLabel{l, now, gs, os}, rest} == FA.get_req.label_gs(l, now, _) : Wr.Dec<FA.Req>}
      %ae.outcomes(os, rest, ho) : {Wr.Got{FA.QLabel{l, now, gs, os}, rest} == FA.get_req.label_os(l, now, gs, _) : Wr.Dec<FA.Req>}
      {==}
    case FA.QExit{+base, +now, +slots, +gs, +os}:
      +hq = h
      +hb = LVE.ve.and_l(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os)))), hq)
      +h2 = LVE.ve.and_r(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os)))), hq)
      +hn = LVE.ve.and_l(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os))), h2)
      +h3 = LVE.ve.and_r(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os))), h2)
      +hs = LVE.ve.and_l(SVW.fit_slots(slots), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os)), h3)
      +h4 = LVE.ve.and_r(SVW.fit_slots(slots), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os)), h3)
      +hg = LVE.ve.and_l(SSW.fit_gauges(gs), SAW.fit_outcomes(os), h4)
      +ho = LVE.ve.and_r(SSW.fit_gauges(gs), SAW.fit_outcomes(os), h4)
      %LVE.ve.nat(base, Wr.put_nat(now, SVW.w_slots(slots, SSW.w_gauges(gs, SAW.w_outcomes(os, rest)))), hb) : {Wr.Got{FA.QExit{base, now, slots, gs, os}, rest} == FA.get_req.exit(_) : Wr.Dec<FA.Req>}
      %LVE.ve.nat(now, SVW.w_slots(slots, SSW.w_gauges(gs, SAW.w_outcomes(os, rest))), hn) : {Wr.Got{FA.QExit{base, now, slots, gs, os}, rest} == FA.get_req.exit_now(base, _) : Wr.Dec<FA.Req>}
      %LVE.ve.slots(slots, SSW.w_gauges(gs, SAW.w_outcomes(os, rest)), hs) : {Wr.Got{FA.QExit{base, now, slots, gs, os}, rest} == FA.get_req.exit_slots(base, now, _) : Wr.Dec<FA.Req>}
      %LSE.se.gauges(gs, SAW.w_outcomes(os, rest), hg) : {Wr.Got{FA.QExit{base, now, slots, gs, os}, rest} == FA.get_req.exit_gs(base, now, slots, _) : Wr.Dec<FA.Req>}
      %ae.outcomes(os, rest, ho) : {Wr.Got{FA.QExit{base, now, slots, gs, os}, rest} == FA.get_req.exit_os(base, now, slots, gs, _) : Wr.Dec<FA.Req>}
      {==}

# Replies: the encoders are the spec spellers
# ------------------------------------------

def ae.put_outcome(o: At.Outcome) -> {FA.put_outcome(o, "") == Wr.put_nat(SAW.w_outcome(o), "") : String}:
  match o:
    case At.Survived{}:
      {==}
    case At.Clean{}:
      {==}
    case At.Unrun{}:
      {==}

# the reply of a request is the spec's spelling of the model's decision
def ae.answer(q: FA.Req) -> {FA.answer(q) == SAW.w_reply(q) : String}:
  match q:
    case FA.QOutcome{r}:
      ae.put_outcome(At.outcome(r))
    case FA.QLabel{l, now, gs, os}:
      LSE.se.put_label(At.label(l, now, gs, os), "")
    case FA.QExit{base, now, slots, gs, os}:
      {==}
