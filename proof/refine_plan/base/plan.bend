# eukhe: lemmas of the refine_plan plan proofs: one more edit is one more
# row, decided after the rows before it (rpp.rows, rpp.fold); the change
# lines are those of the applied rows (rpp.changes)

import Base
import ../../../bend/refine_plan.bend as Rp
import ../../../laws/refine_plan/model.bend as RefinePlan
import ../../../laws/refine_plan/plan.bend as RefinePlanPlan

# Earlier edits
# -------------

# the writes and removals the code threads after the edits xs
def rpp.T(+o: Rp.Opts, xs: List<&2, Rp.Ed>, +ts: List<&2, Rp.Touch>) -> List<&2, Rp.Touch>:
  match xs:
    case Nil{}:
      ts
    case +x <> t:
      rpp.T(o, t, Rp.touch(Rp.row(o, x, ts), ts))

# one more edit is one more row, decided after the edits before it
def rpp.snoc(+o: Rp.Opts, xs: List<&2, Rp.Ed>, +e: Rp.Ed, +ts: List<&2, Rp.Touch>) -> {Rp.plan.rows(o, List.append(&2, Rp.Ed, xs, [e]), ts) == List.append(&2, Rp.Row, Rp.plan.rows(o, xs, ts), [Rp.row(o, e, rpp.T(o, xs, ts))]) : List<&2, Rp.Row>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      +ts2 = Rp.touch(Rp.row(o, x, ts), ts)
      Equal.cong(List<&2, Rp.Row>, List<&2, Rp.Row>, l => Rp.row(o, x, ts) <> l, Rp.plan.rows(o, List.append(&2, Rp.Ed, t, [e]), ts2), List.append(&2, Rp.Row, Rp.plan.rows(o, t, ts2), [Rp.row(o, e, rpp.T(o, t, ts2))]), rpp.snoc(o, t, e, ts2))

def rpp.same(a: Rp.Comp, b: Rp.Comp) -> {Rp.comp_eq(a, b) == RefinePlanPlan.rs_same(a, b) : Bool}:
  match a:
    case Rp.KPrompt{}:
      match b:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}
    case Rp.KMemory{}:
      match b:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}
    case Rp.KSkill{}:
      match b:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}
    case Rp.KSubagent{}:
      match b:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}
    case Rp.KFactory{}:
      match b:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}

def rpp.at(h: Bool, p: Bool, acc: Maybe<&2, Bool>) -> {Rp.lookup.at(h, p, acc) == RefinePlanPlan.rs_left.at(h, p, acc) : Maybe<&2, Bool>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def rpp.hit(+rc: Rp.Comp, +rid: String, +c: Rp.Comp, +id: String, +p: Bool, +acc: Maybe<&2, Bool>) -> {Rp.lookup.at(Bool.and(Rp.comp_eq(rc, c), String.eq(rid, id)), p, acc) == RefinePlanPlan.rs_left.at(Bool.and(RefinePlanPlan.rs_same(rc, c), String.eq(rid, id)), p, acc) : Maybe<&2, Bool>}:
  %rpp.same(rc, c) : {Rp.lookup.at(Bool.and(Rp.comp_eq(rc, c), String.eq(rid, id)), p, acc) == RefinePlanPlan.rs_left.at(Bool.and(_, String.eq(rid, id)), p, acc) : Maybe<&2, Bool>}
  rpp.at(Bool.and(Rp.comp_eq(rc, c), String.eq(rid, id)), p, acc)

# a row's write or removal: the code's lookup after it is the spec's
def rpp.touch(r: Rp.Row, +ts: List<&2, Rp.Touch>, +c: Rp.Comp, +id: String) -> {Rp.lookup(Rp.touch(r, ts), c, id) == RefinePlanPlan.rs_left.row(r, c, id, Rp.lookup(ts, c, id)) : Maybe<&2, Bool>}:
  match r:
    case Rp.Row{rv, +rc, +rid, x}:
      match x:
        case Rp.OInvalid{m}:
          {==}
        case Rp.ORefused{m}:
          {==}
        case Rp.ORemoved{}:
          rpp.hit(rc, rid, c, id, False{}, Rp.lookup(ts, c, id))
        case Rp.OWritten{}:
          rpp.hit(rc, rid, c, id, True{}, Rp.lookup(ts, c, id))

# the code's lookup after the edits xs is the spec's scan of their rows
def rpp.look(+o: Rp.Opts, xs: List<&2, Rp.Ed>, +ts: List<&2, Rp.Touch>, +c: Rp.Comp, +id: String) -> {Rp.lookup(rpp.T(o, xs, ts), c, id) == RefinePlanPlan.rs_left.go(Rp.plan.rows(o, xs, ts), c, id, Rp.lookup(ts, c, id)) : Maybe<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      +ts2 = Rp.touch(Rp.row(o, x, ts), ts)
      Equal.trans(Maybe<&2, Bool>, Rp.lookup(rpp.T(o, t, ts2), c, id), RefinePlanPlan.rs_left.go(Rp.plan.rows(o, t, ts2), c, id, Rp.lookup(ts2, c, id)), RefinePlanPlan.rs_left.go(Rp.plan.rows(o, t, ts2), c, id, RefinePlanPlan.rs_left.row(Rp.row(o, x, ts), c, id, Rp.lookup(ts, c, id))), rpp.look(o, t, ts2, c, id), Equal.cong(Maybe<&2, Bool>, Maybe<&2, Bool>, a => RefinePlanPlan.rs_left.go(Rp.plan.rows(o, t, ts2), c, id, a), Rp.lookup(ts2, c, id), RefinePlanPlan.rs_left.row(Rp.row(o, x, ts), c, id, Rp.lookup(ts, c, id)), rpp.touch(Rp.row(o, x, ts), ts, c, id)))

# One row
# -------

def rpp.bad(e: Rp.Ed) -> {Rp.invalid_verb(e) == RefinePlanPlan.rs_bad_verb(e) : Rp.Verb}:
  match e:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      match verb:
        case None{}:
          match comp:
            case None{}:
              {==}
            case Some{c}:
              {==}
        case Some{v}:
          match comp:
            case None{}:
              {==}
            case Some{c}:
              {==}

def rpp.kind(e: Rp.Ed) -> {Rp.comp_of(e) == RefinePlanPlan.rs_kind(e) : Rp.Comp}:
  match e:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      match comp:
        case None{}:
          {==}
        case Some{c}:
          {==}

def rpp.final(v: Rp.Verb, p: Bool) -> {Rp.out.final(v, p) == RefinePlanPlan.rs_final(v, p) : Rp.Out}:
  match v:
    case Rp.ACreate{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case Rp.AUpdate{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case Rp.ADelete{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}

def rpp.gate(v: Rp.Verb, c: Rp.Comp, +f: Bool) -> {Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.not(f))) == Bool.and(RefinePlan.rs_is_factory(c), Bool.and(Bool.not(RefinePlan.rs_is_delete(v)), Bool.not(f))) : Bool}:
  match v:
    case Rp.ACreate{}:
      match c:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}
    case Rp.AUpdate{}:
      match c:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}
    case Rp.ADelete{}:
      match c:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}

def rpp.ofirst.same(b: Bool, +m: String, r: Rp.Out, -R: Maybe<&2, String>, -f: Rp.Out, er: {r == RefinePlanPlan.rs_decide.at(R, f) : Rp.Out}) -> {Rp.out.first(b, m, r) == RefinePlanPlan.rs_decide.at(RefinePlan.rs_first.at(RefinePlan.RsRule{b, m}, R), f) : Rp.Out}:
  match b:
    case True{}:
      {==}
    case False{}:
      er

def rpp.ofirst(+b1: Bool, -b2: Bool, eb: {b1 == b2 : Bool}, +m: String, +r: Rp.Out, +R: Maybe<&2, String>, +f: Rp.Out, +er: {r == RefinePlanPlan.rs_decide.at(R, f) : Rp.Out}) -> {Rp.out.first(b1, m, r) == RefinePlanPlan.rs_decide.at(RefinePlan.rs_first.at(RefinePlan.RsRule{b2, m}, R), f) : Rp.Out}:
  %eb : {Rp.out.first(b1, m, r) == RefinePlanPlan.rs_decide.at(RefinePlan.rs_first.at(RefinePlan.RsRule{_, m}, R), f) : Rp.Out}
  rpp.ofirst.same(b1, m, r, R, f, er)

def rpp.decide(o: Rp.Opts, e: Rp.Ed, +v: Rp.Verb, +c: Rp.Comp, +look: Maybe<&2, Bool>) -> {Rp.decide(o, e, v, c, look) == RefinePlanPlan.rs_decide(o, e, v, c, look) : Rp.Out}:
  match o:
    case Rp.Opts{+factory, +baseline}:
      match e:
        case Rp.Ed{verb, comp, id, title, content, pyref, args, +exists, +differs, +held}:
          +p = Maybe.default(&2, Bool, look, exists)
          +m1 = {"entry changed during refinement planning" : String}
          +m2 = {"the factory is disabled; run /factory on to enable it" : String}
          +m3 = {"eukhe's memory is the chat: say it in your reply" : String}
          +b1 = Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs))
          +b2 = Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.not(factory)))
          +s2 = Bool.and(RefinePlan.rs_is_factory(c), Bool.and(Bool.not(RefinePlan.rs_is_delete(v)), Bool.not(factory)))
          +c3 = Rp.out.first(Bool.not(held), m3, Rp.out.final(v, p))
          +R3 = RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(held), m3}, None{})
          +p3 = rpp.ofirst.same(Bool.not(held), m3, Rp.out.final(v, p), None{}, RefinePlanPlan.rs_final(v, p), rpp.final(v, p))
          +c2 = Rp.out.first(b2, m2, c3)
          +R2 = RefinePlan.rs_first.at(RefinePlan.RsRule{s2, m2}, R3)
          +p2 = rpp.ofirst(b2, s2, rpp.gate(v, c, factory), m2, c3, R3, RefinePlanPlan.rs_final(v, p), p3)
          rpp.ofirst.same(b1, m1, c2, R2, RefinePlanPlan.rs_final(v, p), p2)

def rpp.row.at(+o: Rp.Opts, +pre: List<&2, Rp.Ed>, +e: Rp.Ed, +id: String, k: Rp.Check) -> {Rp.row.at(o, e, rpp.T(o, pre, []), id, k) == RefinePlanPlan.rs_row.at(o, Rp.plan.rows(o, pre, []), e, id, k) : Rp.Row}:
  match k:
    case Rp.CBad{+msg}:
      %rpp.bad(e) : {Rp.row.at(o, e, rpp.T(o, pre, []), id, Rp.CBad{msg}) == Rp.Row{_, RefinePlanPlan.rs_kind(e), id, Rp.OInvalid{msg}} : Rp.Row}
      %rpp.kind(e) : {Rp.row.at(o, e, rpp.T(o, pre, []), id, Rp.CBad{msg}) == Rp.Row{Rp.invalid_verb(e), _, id, Rp.OInvalid{msg}} : Rp.Row}
      {==}
    case Rp.COk{+v, +c}:
      %Equal.sym(Maybe<&2, Bool>, Rp.lookup(rpp.T(o, pre, []), c, id), RefinePlanPlan.rs_left.go(Rp.plan.rows(o, pre, []), c, id, None{}), rpp.look(o, pre, [], c, id)) : {Rp.Row{v, c, id, Rp.decide(o, e, v, c, _)} == RefinePlanPlan.rs_row.at(o, Rp.plan.rows(o, pre, []), e, id, Rp.COk{v, c}) : Rp.Row}
      Equal.cong(Rp.Out, Rp.Row, x => Rp.Row{v, c, id, x}, Rp.decide(o, e, v, c, RefinePlanPlan.rs_left(Rp.plan.rows(o, pre, []), c, id)), RefinePlanPlan.rs_decide(o, e, v, c, RefinePlanPlan.rs_left(Rp.plan.rows(o, pre, []), c, id)), rpp.decide(o, e, v, c, RefinePlanPlan.rs_left(Rp.plan.rows(o, pre, []), c, id)))

def rpp.rows(+o: Rp.Opts, +pre: List<&2, Rp.Ed>, +e: Rp.Ed) -> {RefinePlanPlan.rs_rows(Rp.plan(o, List.append(&2, Rp.Ed, pre, [e]))) == List.append(&2, Rp.Row, RefinePlanPlan.rs_rows(Rp.plan(o, pre)), [RefinePlanPlan.rs_row(o, RefinePlanPlan.rs_rows(Rp.plan(o, pre)), e)]) : List<&2, Rp.Row>}:
  %Equal.sym(List<&2, Rp.Row>, Rp.plan.rows(o, List.append(&2, Rp.Ed, pre, [e]), []), List.append(&2, Rp.Row, Rp.plan.rows(o, pre, []), [Rp.row(o, e, rpp.T(o, pre, []))]), rpp.snoc(o, pre, e, [])) : {_ == List.append(&2, Rp.Row, Rp.plan.rows(o, pre, []), [RefinePlanPlan.rs_row(o, Rp.plan.rows(o, pre, []), e)]) : List<&2, Rp.Row>}
  Equal.cong(Rp.Row, List<&2, Rp.Row>, r => List.append(&2, Rp.Row, Rp.plan.rows(o, pre, []), [r]), Rp.row(o, e, rpp.T(o, pre, [])), RefinePlanPlan.rs_row(o, Rp.plan.rows(o, pre, []), e), rpp.row.at(o, pre, e, Maybe.default(&2, String, Rp.computed(e), ""), Rp.check(e, Rp.computed(e))))

# Change lines
# ------------

def rpp.line(v: Rp.Verb, c: Rp.Comp, +id: String) -> {String.concat([Rp.verb_name(v), " ", Rp.comp_name(c), ":", id]) == RefinePlanPlan.rs_line(Rp.Row{v, c, id, Rp.ORemoved{}}) : String}:
  match v:
    case Rp.ACreate{}:
      match c:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}
    case Rp.AUpdate{}:
      match c:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}
    case Rp.ADelete{}:
      match c:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}

def rpp.lines(rows: List<&2, Rp.Row>) -> {Rp.changes(rows) == RefinePlanPlan.rs_lines(rows) : List<&2, String>}:
  match rows:
    case Nil{}:
      {==}
    case w <> t:
      match w:
        case Rp.Row{+v, +c, +id, x}:
          match x:
            case Rp.OInvalid{m}:
              rpp.lines(t)
            case Rp.ORefused{m}:
              rpp.lines(t)
            case Rp.ORemoved{}:
              %rpp.lines(t) : {String.concat([Rp.verb_name(v), " ", Rp.comp_name(c), ":", id]) <> Rp.changes(t) == RefinePlanPlan.rs_line(Rp.Row{v, c, id, Rp.ORemoved{}}) <> _ : List<&2, String>}
              Equal.cong(String, List<&2, String>, s => s <> Rp.changes(t), String.concat([Rp.verb_name(v), " ", Rp.comp_name(c), ":", id]), RefinePlanPlan.rs_line(Rp.Row{v, c, id, Rp.ORemoved{}}), rpp.line(v, c, id))
            case Rp.OWritten{}:
              %rpp.lines(t) : {String.concat([Rp.verb_name(v), " ", Rp.comp_name(c), ":", id]) <> Rp.changes(t) == RefinePlanPlan.rs_line(Rp.Row{v, c, id, Rp.OWritten{}}) <> _ : List<&2, String>}
              Equal.cong(String, List<&2, String>, s => s <> Rp.changes(t), String.concat([Rp.verb_name(v), " ", Rp.comp_name(c), ":", id]), RefinePlanPlan.rs_line(Rp.Row{v, c, id, Rp.ORemoved{}}), rpp.line(v, c, id))

def rpp.changes(+o: Rp.Opts, +eds: List<&2, Rp.Ed>) -> {RefinePlanPlan.rs_changes(Rp.plan(o, eds)) == RefinePlanPlan.rs_lines(RefinePlanPlan.rs_rows(Rp.plan(o, eds))) : List<&2, String>}:
  rpp.lines(Rp.plan.rows(o, eds, []))

# Rows, edit by edit
# ------------------

def rpp.app_nil(a: List<&2, Rp.Ed>) -> {List.append(&2, Rp.Ed, a, []) == a : List<&2, Rp.Ed>}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Rp.Ed>, List<&2, Rp.Ed>, l => h <> l, List.append(&2, Rp.Ed, t, []), t, rpp.app_nil(t))

def rpp.app_snoc(a: List<&2, Rp.Ed>, -e: Rp.Ed, -t: List<&2, Rp.Ed>) -> {List.append(&2, Rp.Ed, List.append(&2, Rp.Ed, a, [e]), t) == List.append(&2, Rp.Ed, a, e <> t) : List<&2, Rp.Ed>}:
  match a:
    case Nil{}:
      {==}
    case h <> r:
      Equal.cong(List<&2, Rp.Ed>, List<&2, Rp.Ed>, l => h <> l, List.append(&2, Rp.Ed, List.append(&2, Rp.Ed, r, [e]), t), List.append(&2, Rp.Ed, r, e <> t), rpp.app_snoc(r, e, t))

# the rows after the edits pre, then t: the spec's rows of t from those of pre
def rpp.fold(t: List<&2, Rp.Ed>, +o: Rp.Opts, +pre: List<&2, Rp.Ed>) -> {RefinePlanPlan.rs_rows(Rp.plan(o, List.append(&2, Rp.Ed, pre, t))) == RefinePlanPlan.rs_plan.go(t, o, RefinePlanPlan.rs_rows(Rp.plan(o, pre))) : List<&2, Rp.Row>}:
  match t:
    case Nil{}:
      %Equal.sym(List<&2, Rp.Ed>, List.append(&2, Rp.Ed, pre, []), pre, rpp.app_nil(pre)) : {RefinePlanPlan.rs_rows(Rp.plan(o, _)) == RefinePlanPlan.rs_rows(Rp.plan(o, pre)) : List<&2, Rp.Row>}
      {==}
    case +e <> +r:
      +R = RefinePlanPlan.rs_rows(Rp.plan(o, pre))
      %rpp.app_snoc(pre, e, r) : {RefinePlanPlan.rs_rows(Rp.plan(o, _)) == RefinePlanPlan.rs_plan.go(r, o, List.append(&2, Rp.Row, R, [RefinePlanPlan.rs_row(o, R, e)])) : List<&2, Rp.Row>}
      Equal.trans(List<&2, Rp.Row>, RefinePlanPlan.rs_rows(Rp.plan(o, List.append(&2, Rp.Ed, List.append(&2, Rp.Ed, pre, [e]), r))), RefinePlanPlan.rs_plan.go(r, o, RefinePlanPlan.rs_rows(Rp.plan(o, List.append(&2, Rp.Ed, pre, [e])))), RefinePlanPlan.rs_plan.go(r, o, List.append(&2, Rp.Row, R, [RefinePlanPlan.rs_row(o, R, e)])), rpp.fold(r, o, List.append(&2, Rp.Ed, pre, [e])), Equal.cong(List<&2, Rp.Row>, List<&2, Rp.Row>, l => RefinePlanPlan.rs_plan.go(r, o, l), RefinePlanPlan.rs_rows(Rp.plan(o, List.append(&2, Rp.Ed, pre, [e]))), List.append(&2, Rp.Row, R, [RefinePlanPlan.rs_row(o, R, e)]), rpp.rows(o, pre, e)))
