# eukhe: lemmas of the entry proofs of area goal_text: the reply encoders
# are the spec spellers, a spelled request reads back (gte.*_rt), and a
# decoded one is spelled (gtx.*: a predicate per decoder answer, carried
# stage by stage with the wire exactness lemmas dcw.nat, dcw.str and
# wire_bool_exact)

import Base
import ../../../bend/goal_text.bend as Gt
import ../../../bend/ffi_goal_text.bend as FGt
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/goal_text.bend as GoalText
import ../../base/wire.bend as LWire
import ../../base/wire_dec.bend as LE
import ../../base/staging.bend as LStg
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# Encoders
# --------

def gte.ms(m: Maybe<&2, String>, rest: String) -> {FGt.put_ms(m, rest) == GoalText.gt_w_ms(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def gte.host(m: Maybe<&2, Gt.Host>) -> {FGt.put_host(m) == GoalText.gt_w_host(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{h}:
      match h:
        case Gt.Host{+r, +p}:
          %Equal.sym(String, FGt.put_ms(p, ""), GoalText.gt_w_ms(p, ""), gte.ms(p, "")) : {Wr.put_nat(1n, FGt.put_ms(r, _)) == Wr.put_nat(1n, GoalText.gt_w_ms(r, GoalText.gt_w_ms(p, ""))) : String}
          %Equal.sym(String, FGt.put_ms(r, GoalText.gt_w_ms(p, "")), GoalText.gt_w_ms(r, GoalText.gt_w_ms(p, "")), gte.ms(r, GoalText.gt_w_ms(p, ""))) : {Wr.put_nat(1n, _) == Wr.put_nat(1n, GoalText.gt_w_ms(r, GoalText.gt_w_ms(p, ""))) : String}
          {==}

# Round trips
# -----------

def gte.ms_rt(m: Maybe<&2, String>, +rest: String, h: {GoalText.gt_fit_ms(m) == True{} : Bool}) -> {FGt.get_ms(GoalText.gt_w_ms(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FGt.get_ms.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

def gte.obj_rt(st: Gt.Status, +o: Maybe<&2, String>, +b: Maybe<&2, String>, +u: String, +t: String, +rest: String, h: {GoalText.gt_fit_goal(Gt.Goal{st, o, b, u, t}) == True{} : Bool}) -> {FGt.get_goal.obj(st, FGt.get_ms(GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, Wr.put_str(u, Wr.put_str(t, rest)))))) == Wr.Got{Gt.Goal{st, o, b, u, t}, rest} : Wr.Dec<Gt.Goal>}:
  +h0 = h
  +ho = LLogicBool.tree.pt.and_l(GoalText.gt_fit_ms(o), Bool.and(GoalText.gt_fit_ms(b), Bool.and(LawsBase.wire_fits(String.length(u)), LawsBase.wire_fits(String.length(t)))), h0)
  +h1 = LLogicBool.tree.pt.and_r(GoalText.gt_fit_ms(o), Bool.and(GoalText.gt_fit_ms(b), Bool.and(LawsBase.wire_fits(String.length(u)), LawsBase.wire_fits(String.length(t)))), h0)
  +hb = LLogicBool.tree.pt.and_l(GoalText.gt_fit_ms(b), Bool.and(LawsBase.wire_fits(String.length(u)), LawsBase.wire_fits(String.length(t))), h1)
  +h2 = LLogicBool.tree.pt.and_r(GoalText.gt_fit_ms(b), Bool.and(LawsBase.wire_fits(String.length(u)), LawsBase.wire_fits(String.length(t))), h1)
  +hu = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(u)), LawsBase.wire_fits(String.length(t)), h2)
  +ht = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(u)), LawsBase.wire_fits(String.length(t)), h2)
  %Equal.sym(Wr.Dec<Maybe<&2, String>>, FGt.get_ms(GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, Wr.put_str(u, Wr.put_str(t, rest))))), Wr.Got{o, GoalText.gt_w_ms(b, Wr.put_str(u, Wr.put_str(t, rest)))}, gte.ms_rt(o, GoalText.gt_w_ms(b, Wr.put_str(u, Wr.put_str(t, rest))), ho)) : {FGt.get_goal.obj(st, _) == Wr.Got{Gt.Goal{st, o, b, u, t}, rest} : Wr.Dec<Gt.Goal>}
  %Equal.sym(Wr.Dec<Maybe<&2, String>>, FGt.get_ms(GoalText.gt_w_ms(b, Wr.put_str(u, Wr.put_str(t, rest)))), Wr.Got{b, Wr.put_str(u, Wr.put_str(t, rest))}, gte.ms_rt(b, Wr.put_str(u, Wr.put_str(t, rest)), hb)) : {FGt.get_goal.budget(st, o, _) == Wr.Got{Gt.Goal{st, o, b, u, t}, rest} : Wr.Dec<Gt.Goal>}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(u, Wr.put_str(t, rest))), Wr.Got{u, Wr.put_str(t, rest)}, Wire.wire_str_round_trip(u, Wr.put_str(t, rest), hu)) : {FGt.get_goal.used(st, o, b, _) == Wr.Got{Gt.Goal{st, o, b, u, t}, rest} : Wr.Dec<Gt.Goal>}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(t, rest)), Wr.Got{t, rest}, Wire.wire_str_round_trip(t, rest, ht)) : {FGt.get_goal.secs(st, o, b, u, _) == Wr.Got{Gt.Goal{st, o, b, u, t}, rest} : Wr.Dec<Gt.Goal>}
  {==}

def gte.goal_rt(g: Gt.Goal, +rest: String, h: {GoalText.gt_fit_goal(g) == True{} : Bool}) -> {FGt.get_goal(GoalText.gt_w_goal(g, rest)) == Wr.Got{g, rest} : Wr.Dec<Gt.Goal>}:
  match g:
    case Gt.Goal{s, +o, +b, +u, +t}:
      match s:
        case Gt.SIdle{}:
          gte.obj_rt(Gt.SIdle{}, o, b, u, t, rest, h)
        case Gt.SActive{}:
          gte.obj_rt(Gt.SActive{}, o, b, u, t, rest, h)
        case Gt.SPaused{}:
          gte.obj_rt(Gt.SPaused{}, o, b, u, t, rest, h)
        case Gt.SBudgetLimited{}:
          gte.obj_rt(Gt.SBudgetLimited{}, o, b, u, t, rest, h)
        case Gt.SComplete{}:
          gte.obj_rt(Gt.SComplete{}, o, b, u, t, rest, h)
        case Gt.SError{}:
          gte.obj_rt(Gt.SError{}, o, b, u, t, rest, h)

def gte.req_rt(q: FGt.Req, +rest: String, h: {GoalText.gt_fit_req(q) == True{} : Bool}) -> {FGt.get_req(GoalText.gt_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FGt.Req>}:
  match q:
    case FGt.QPrompt{k, +g}:
      match k:
        case Gt.KContinuation{}:
          %Equal.sym(Wr.Dec<Gt.Goal>, FGt.get_goal(GoalText.gt_w_goal(g, rest)), Wr.Got{g, rest}, gte.goal_rt(g, rest, h)) : {FGt.get_prompt(Gt.KContinuation{}, _) == Wr.Got{FGt.QPrompt{Gt.KContinuation{}, g}, rest} : Wr.Dec<FGt.Req>}
          {==}
        case Gt.KBudgetLimit{}:
          %Equal.sym(Wr.Dec<Gt.Goal>, FGt.get_goal(GoalText.gt_w_goal(g, rest)), Wr.Got{g, rest}, gte.goal_rt(g, rest, h)) : {FGt.get_prompt(Gt.KBudgetLimit{}, _) == Wr.Got{FGt.QPrompt{Gt.KBudgetLimit{}, g}, rest} : Wr.Dec<FGt.Req>}
          {==}
        case Gt.KObjectiveUpdated{}:
          %Equal.sym(Wr.Dec<Gt.Goal>, FGt.get_goal(GoalText.gt_w_goal(g, rest)), Wr.Got{g, rest}, gte.goal_rt(g, rest, h)) : {FGt.get_prompt(Gt.KObjectiveUpdated{}, _) == Wr.Got{FGt.QPrompt{Gt.KObjectiveUpdated{}, g}, rest} : Wr.Dec<FGt.Req>}
          {==}
    case FGt.QUsage{+g}:
      %Equal.sym(Wr.Dec<Gt.Goal>, FGt.get_goal(GoalText.gt_w_goal(g, rest)), Wr.Got{g, rest}, gte.goal_rt(g, rest, h)) : {FGt.get_usage(_) == Wr.Got{FGt.QUsage{g}, rest} : Wr.Dec<FGt.Req>}
      {==}
    case FGt.QHost{+g, +a}:
      %Equal.sym(Wr.Dec<Gt.Goal>, FGt.get_goal(GoalText.gt_w_goal(g, Wr.put_bool(a, rest))), Wr.Got{g, Wr.put_bool(a, rest)}, gte.goal_rt(g, Wr.put_bool(a, rest), h)) : {FGt.get_host(_) == Wr.Got{FGt.QHost{g, a}, rest} : Wr.Dec<FGt.Req>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(a, rest)), Wr.Got{a, rest}, Wire.wire_bool_round_trip(a, rest)) : {FGt.get_ask(g, _) == Wr.Got{FGt.QHost{g, a}, rest} : Wr.Dec<FGt.Req>}
      {==}

# Replies never open with 'E'
# ---------------------------

def gte.ms_ok(m: Maybe<&2, String>) -> {LawsBase.wire_opens_err(FGt.put_ms(m, "")) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def gte.host_ok(m: Maybe<&2, Gt.Host>) -> {LawsBase.wire_opens_err(FGt.put_host(m)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{h}:
      match h:
        case Gt.Host{r, p}:
          {==}

def gte.answer_ok(q: FGt.Req) -> {LawsBase.wire_opens_err(FGt.answer(q)) == False{} : Bool}:
  match q:
    case FGt.QPrompt{k, g}:
      LE.dcw.sfin_ok(Wr.put_str.go(Gt.prompt(k, g), SNil{}, 0n), "")
    case FGt.QUsage{g}:
      gte.ms_ok(Gt.usage(g))
    case FGt.QHost{g, a}:
      gte.host_ok(Gt.host(g, a))

# Decoded requests are spelled
# ----------------------------

def gtx.MS(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == GoalText.gt_w_ms(m, r) : String} & {GoalText.gt_fit_ms(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def gtx.ms_some(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> gtx.MS(s, FGt.get_ms.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, fit) = sp
      (LE.dcw.after(s, 1n, s1, Wr.put_str(x, r), pre, e), fit)
    case Wr.Bad{}:
      Unit{}

def gtx.ms_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> gtx.MS(s, FGt.get_ms.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (np, {==})
        case 1n:
          gtx.ms_some(s, s1, np, Wr.get_str(s1), LE.dcw.str(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a Maybe<String> decoded is spelled, and fits
def gtx.ms(+s: String) -> gtx.MS(s, FGt.get_ms(s)):
  gtx.ms_at(s, Wr.get_nat(s), LE.dcw.nat(s))

def gtx.GP(s: String, d: Wr.Dec<Gt.Goal>) -> Type:
  match d:
    case Wr.Got{g, r}:
      {s == GoalText.gt_w_goal(g, r) : String} & {GoalText.gt_fit_goal(g) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def gtx.secs(-s: String, st: Gt.Status, +o: Maybe<&2, String>, +b: Maybe<&2, String>, +u: String, -s4: String, pre: {s == Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, Wr.put_str(u, s4)))) : String}, +fob: {Bool.and(GoalText.gt_fit_ms(o), GoalText.gt_fit_ms(b)) == True{} : Bool}, fu: {LawsBase.wire_fits(String.length(u)) == True{} : Bool}, d: Wr.Dec<String>, sp: LE.dcw.SP(s4, d)) -> gtx.GP(s, FGt.get_goal.secs(st, o, b, u, d)):
  match d:
    case Wr.Got{+t, +r}:
      (e, ft) = sp
      +fo = LLogicBool.tree.pt.and_l(GoalText.gt_fit_ms(o), GoalText.gt_fit_ms(b), fob)
      +fb = LLogicBool.tree.pt.and_r(GoalText.gt_fit_ms(o), GoalText.gt_fit_ms(b), fob)
      (Equal.trans(String, s, Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, Wr.put_str(u, s4)))), Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, Wr.put_str(u, Wr.put_str(t, r))))), pre, Equal.cong(String, String, z => Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, Wr.put_str(u, z)))), s4, Wr.put_str(t, r), e)),
        LBool.cb_and_intro(GoalText.gt_fit_ms(o), Bool.and(GoalText.gt_fit_ms(b), Bool.and(LawsBase.wire_fits(String.length(u)), LawsBase.wire_fits(String.length(t)))), fo, LBool.cb_and_intro(GoalText.gt_fit_ms(b), Bool.and(LawsBase.wire_fits(String.length(u)), LawsBase.wire_fits(String.length(t))), fb, LBool.cb_and_intro(LawsBase.wire_fits(String.length(u)), LawsBase.wire_fits(String.length(t)), fu, ft))))
    case Wr.Bad{}:
      Unit{}

def gtx.used(-s: String, st: Gt.Status, +o: Maybe<&2, String>, +b: Maybe<&2, String>, -s3: String, pre: {s == Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, s3))) : String}, fob: {Bool.and(GoalText.gt_fit_ms(o), GoalText.gt_fit_ms(b)) == True{} : Bool}, d: Wr.Dec<String>, sp: LE.dcw.SP(s3, d)) -> gtx.GP(s, FGt.get_goal.used(st, o, b, d)):
  match d:
    case Wr.Got{+u, +r}:
      (e, fu) = sp
      +pre2 = Equal.trans(String, s, Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, s3))), Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, Wr.put_str(u, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, z))), s3, Wr.put_str(u, r), e))
      gtx.secs(s, st, o, b, u, r, pre2, fob, fu, Wr.get_str(r), LE.dcw.str(r))
    case Wr.Bad{}:
      Unit{}

def gtx.budget(-s: String, st: Gt.Status, +o: Maybe<&2, String>, -s2: String, pre: {s == Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, s2)) : String}, fo: {GoalText.gt_fit_ms(o) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, mp: gtx.MS(s2, d)) -> gtx.GP(s, FGt.get_goal.budget(st, o, d)):
  match d:
    case Wr.Got{+b, +r}:
      (e, fb) = mp
      +pre2 = Equal.trans(String, s, Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, s2)), Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, GoalText.gt_w_ms(b, r))), pre, Equal.cong(String, String, z => Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, z)), s2, GoalText.gt_w_ms(b, r), e))
      gtx.used(s, st, o, b, r, pre2, LBool.cb_and_intro(GoalText.gt_fit_ms(o), GoalText.gt_fit_ms(b), fo, fb), Wr.get_str(r), LE.dcw.str(r))
    case Wr.Bad{}:
      Unit{}

def gtx.obj(-s: String, st: Gt.Status, -s1: String, pre: {s == Wr.put_nat(GoalText.gt_w_status(st), s1) : String}, d: Wr.Dec<Maybe<&2, String>>, mp: gtx.MS(s1, d)) -> gtx.GP(s, FGt.get_goal.obj(st, d)):
  match d:
    case Wr.Got{+o, +r}:
      (e, fo) = mp
      +pre2 = Equal.trans(String, s, Wr.put_nat(GoalText.gt_w_status(st), s1), Wr.put_nat(GoalText.gt_w_status(st), GoalText.gt_w_ms(o, r)), pre, Equal.cong(String, String, z => Wr.put_nat(GoalText.gt_w_status(st), z), s1, GoalText.gt_w_ms(o, r), e))
      gtx.budget(s, st, o, r, pre2, fo, FGt.get_ms(r), gtx.ms(r))
    case Wr.Bad{}:
      Unit{}

def gtx.goal_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> gtx.GP(s, FGt.get_goal.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          gtx.obj(s, Gt.SIdle{}, s1, np, FGt.get_ms(s1), gtx.ms(s1))
        case 1n:
          gtx.obj(s, Gt.SActive{}, s1, np, FGt.get_ms(s1), gtx.ms(s1))
        case 2n:
          gtx.obj(s, Gt.SPaused{}, s1, np, FGt.get_ms(s1), gtx.ms(s1))
        case 3n:
          gtx.obj(s, Gt.SBudgetLimited{}, s1, np, FGt.get_ms(s1), gtx.ms(s1))
        case 4n:
          gtx.obj(s, Gt.SComplete{}, s1, np, FGt.get_ms(s1), gtx.ms(s1))
        case 5n:
          gtx.obj(s, Gt.SError{}, s1, np, FGt.get_ms(s1), gtx.ms(s1))
        case 6n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a goal decoded is spelled, and fits
def gtx.goal(+s: String) -> gtx.GP(s, FGt.get_goal(s)):
  gtx.goal_at(s, Wr.get_nat(s), LE.dcw.nat(s))

def gtx.RP(s: String, d: Wr.Dec<FGt.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == GoalText.gt_w_req(q, r) : String} & {GoalText.gt_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def gtx.prompt(-s: String, k: Gt.Prompt, -s2: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(GoalText.gt_w_kind(k), s2)) : String}, d: Wr.Dec<Gt.Goal>, gp: gtx.GP(s2, d)) -> gtx.RP(s, FGt.get_prompt(k, d)):
  match d:
    case Wr.Got{+g, +r}:
      (e, fg) = gp
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(GoalText.gt_w_kind(k), s2)), Wr.put_nat(0n, Wr.put_nat(GoalText.gt_w_kind(k), GoalText.gt_w_goal(g, r))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(GoalText.gt_w_kind(k), z)), s2, GoalText.gt_w_goal(g, r), e)), fg)
    case Wr.Bad{}:
      Unit{}

def gtx.kind.of(t: Nat, -s: String, +s2: String, pre2: {s == Wr.put_nat(0n, Wr.put_nat(t, s2)) : String}) -> gtx.RP(s, FGt.get_kind.tag(t, s2)):
  match t:
    case 0n:
      gtx.prompt(s, Gt.KContinuation{}, s2, pre2, FGt.get_goal(s2), gtx.goal(s2))
    case 1n:
      gtx.prompt(s, Gt.KBudgetLimit{}, s2, pre2, FGt.get_goal(s2), gtx.goal(s2))
    case 2n:
      gtx.prompt(s, Gt.KObjectiveUpdated{}, s2, pre2, FGt.get_goal(s2), gtx.goal(s2))
    case 3n+u:
      Unit{}

def gtx.kind(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, np: LE.dcw.NP(s1, d)) -> gtx.RP(s, FGt.get_kind(d)):
  match d:
    case Wr.Got{+t, +s2}:
      gtx.kind.of(t, s, s2, Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_nat(t, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_nat(t, s2), np)))
    case Wr.Bad{}:
      Unit{}

def gtx.usage(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Gt.Goal>, gp: gtx.GP(s1, d)) -> gtx.RP(s, FGt.get_usage(d)):
  match d:
    case Wr.Got{+g, +r}:
      (e, fg) = gp
      (LE.dcw.after(s, 1n, s1, GoalText.gt_w_goal(g, r), pre, e), fg)
    case Wr.Bad{}:
      Unit{}

def gtx.ask(-s: String, +g: Gt.Goal, +s2: String, pre: {s == Wr.put_nat(2n, GoalText.gt_w_goal(g, s2)) : String}, fg: {GoalText.gt_fit_goal(g) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> gtx.RP(s, FGt.get_ask(g, d)):
  match d:
    case Wr.Got{+a, +r}:
      +e = Wire.wire_bool_exact(s2, a, r, ed)
      (Equal.trans(String, s, Wr.put_nat(2n, GoalText.gt_w_goal(g, s2)), Wr.put_nat(2n, GoalText.gt_w_goal(g, Wr.put_bool(a, r))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, GoalText.gt_w_goal(g, z)), s2, Wr.put_bool(a, r), e)), fg)
    case Wr.Bad{}:
      Unit{}

def gtx.host(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Gt.Goal>, gp: gtx.GP(s1, d)) -> gtx.RP(s, FGt.get_host(d)):
  match d:
    case Wr.Got{+g, +r}:
      (e, fg) = gp
      gtx.ask(s, g, r, LE.dcw.after(s, 2n, s1, GoalText.gt_w_goal(g, r), pre, e), fg, Wr.get_bool(r), {==})
    case Wr.Bad{}:
      Unit{}

def gtx.req_at(+s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> gtx.RP(s, FGt.get_req.start(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          gtx.kind(s, s1, np, Wr.get_nat(s1), LE.dcw.nat(s1))
        case 1n:
          gtx.usage(s, s1, np, FGt.get_goal(s1), gtx.goal(s1))
        case 2n:
          gtx.host(s, s1, np, FGt.get_goal(s1), gtx.goal(s1))
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def gtx.T(s: String) -> Type:
  Sigma<&1, &1, FGt.Req, q => {s == GoalText.gt_w_req(q, "") : String} & {GoalText.gt_fit_req(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def gtx.top(-s: String, d: Wr.Dec<FGt.Req>, rp: gtx.RP(s, d), ok: {LawsBase.wire_opens_err(FGt.ffi.got(d)) == False{} : Bool}) -> gtx.T(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(gtx.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(gtx.T(s), ok)
