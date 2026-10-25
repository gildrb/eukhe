# eukhe: lemmas of area goal_text: each function of bend/goal_text.bend is
# the spec helper of laws/goal_text.bend (by induction on the digits or the
# text it reads, case by case on the Bool or constructor it matches)

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/goal_text.bend as GoalText

def gtb.status_name(s: Gt.Status) -> {Gt.status_name(s) == GoalText.gt_status_name(s) : String}:
  match s:
    case Gt.SIdle{}:
      {==}
    case Gt.SActive{}:
      {==}
    case Gt.SPaused{}:
      {==}
    case Gt.SBudgetLimited{}:
      {==}
    case Gt.SComplete{}:
      {==}
    case Gt.SError{}:
      {==}

# Digits
# ------

def gtb.canon_at(b: Bool, c: Char, t: String, r: String) -> {Gt.canon.at(b, c, t, r) == GoalText.gt_canon.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gtb.canon_go(s: String) -> {Gt.canon.go(s) == GoalText.gt_canon.go(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Gt.canon.go(t), GoalText.gt_canon.go(t), gtb.canon_go(t)) : {Gt.canon.at(Char.is_eq(c, '0'), c, t, _) == GoalText.gt_canon.at(Char.is_eq(c, '0'), c, t, GoalText.gt_canon.go(t)) : String}
      gtb.canon_at(Char.is_eq(c, '0'), c, t, GoalText.gt_canon.go(t))

def gtb.canon_fin(s: String) -> {Gt.canon.fin(s) == GoalText.gt_canon.fin(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def gtb.canon(+s: String) -> {Gt.canon(s) == GoalText.gt_canon(s) : String}:
  %Equal.sym(String, Gt.canon.go(s), GoalText.gt_canon.go(s), gtb.canon_go(s)) : {Gt.canon.fin(_) == GoalText.gt_canon(s) : String}
  gtb.canon_fin(GoalText.gt_canon.go(s))

def gtb.borrow_of(b: Bool) -> {Gt.sub.borrow.of(b) == GoalText.gt_sub.borrow.of(b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gtb.borrow(+x: Nat, +y: Nat, +k: Nat) -> {Gt.sub.borrow(x, y, k) == GoalText.gt_sub.borrow(x, y, k) : Nat}:
  gtb.borrow_of(Nat.is_lt(x, Nat.add(y, k)))

def gtb.sub(a: String, +b: String, +k: Nat) -> {Gt.sub.go(a, b, k) == GoalText.gt_sub.go(a, b, k) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +ta}:
      match b:
        case SNil{}:
          %Equal.sym(Nat, Gt.sub.borrow(Gt.digit(x), 0n, k), GoalText.gt_sub.borrow(Gt.digit(x), 0n, k), gtb.borrow(Gt.digit(x), 0n, k)) : {Gt.sub.of(Gt.digit(x), 0n, k, Gt.sub.go(ta, SNil{}, _)) == GoalText.gt_sub.of(GoalText.gt_digit(x), 0n, k, GoalText.gt_sub.go(ta, SNil{}, GoalText.gt_sub.borrow(GoalText.gt_digit(x), 0n, k))) : String}
          %Equal.sym(String, Gt.sub.go(ta, SNil{}, GoalText.gt_sub.borrow(Gt.digit(x), 0n, k)), GoalText.gt_sub.go(ta, SNil{}, GoalText.gt_sub.borrow(Gt.digit(x), 0n, k)), gtb.sub(ta, SNil{}, GoalText.gt_sub.borrow(Gt.digit(x), 0n, k))) : {Gt.sub.of(Gt.digit(x), 0n, k, _) == GoalText.gt_sub.of(GoalText.gt_digit(x), 0n, k, GoalText.gt_sub.go(ta, SNil{}, GoalText.gt_sub.borrow(GoalText.gt_digit(x), 0n, k))) : String}
          {==}
        case SCon{+y, +tb}:
          %Equal.sym(Nat, Gt.sub.borrow(Gt.digit(x), Gt.digit(y), k), GoalText.gt_sub.borrow(Gt.digit(x), Gt.digit(y), k), gtb.borrow(Gt.digit(x), Gt.digit(y), k)) : {Gt.sub.of(Gt.digit(x), Gt.digit(y), k, Gt.sub.go(ta, tb, _)) == GoalText.gt_sub.of(GoalText.gt_digit(x), GoalText.gt_digit(y), k, GoalText.gt_sub.go(ta, tb, GoalText.gt_sub.borrow(GoalText.gt_digit(x), GoalText.gt_digit(y), k))) : String}
          %Equal.sym(String, Gt.sub.go(ta, tb, GoalText.gt_sub.borrow(Gt.digit(x), Gt.digit(y), k)), GoalText.gt_sub.go(ta, tb, GoalText.gt_sub.borrow(Gt.digit(x), Gt.digit(y), k)), gtb.sub(ta, tb, GoalText.gt_sub.borrow(Gt.digit(x), Gt.digit(y), k))) : {Gt.sub.of(Gt.digit(x), Gt.digit(y), k, _) == GoalText.gt_sub.of(GoalText.gt_digit(x), GoalText.gt_digit(y), k, GoalText.gt_sub.go(ta, tb, GoalText.gt_sub.borrow(GoalText.gt_digit(x), GoalText.gt_digit(y), k))) : String}
          {==}

def gtb.left_of(b: Bool, +budget: String, +used: String) -> {Gt.left.of(b, budget, used) == GoalText.gt_left.of(b, budget, used) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      +go = Gt.sub.go(String.reverse(budget), String.reverse(used), 0n)
      %Equal.sym(String, go, GoalText.gt_sub.go(String.reverse(budget), String.reverse(used), 0n), gtb.sub(String.reverse(budget), String.reverse(used), 0n)) : {Gt.canon(String.reverse(_)) == GoalText.gt_left.of(False{}, budget, used) : String}
      gtb.canon(String.reverse(GoalText.gt_sub.go(String.reverse(budget), String.reverse(used), 0n)))

def gtb.left(+budget: String, +used: String) -> {Gt.left(budget, used) == GoalText.gt_left(budget, used) : String}:
  %Equal.sym(String, Gt.canon(budget), GoalText.gt_canon(budget), gtb.canon(budget)) : {Gt.left.of(Gt.below(_, Gt.canon(used)), _, Gt.canon(used)) == GoalText.gt_left(budget, used) : String}
  %Equal.sym(String, Gt.canon(used), GoalText.gt_canon(used), gtb.canon(used)) : {Gt.left.of(Gt.below(GoalText.gt_canon(budget), _), GoalText.gt_canon(budget), _) == GoalText.gt_left(budget, used) : String}
  gtb.left_of(Gt.below(GoalText.gt_canon(budget), GoalText.gt_canon(used)), GoalText.gt_canon(budget), GoalText.gt_canon(used))

# Text
# ----

def gtb.esc_gt(lt: Bool, gt: Bool, c: Char, r: String) -> {Gt.escape.gt(lt, gt, c, r) == GoalText.gt_escape.gt(lt, gt, c, r) : String}:
  match lt:
    case True{}:
      {==}
    case False{}:
      match gt:
        case True{}:
          {==}
        case False{}:
          {==}

def gtb.esc_lt(amp: Bool, lt: Bool, gt: Bool, c: Char, r: String) -> {Gt.escape.lt(amp, lt, gt, c, r) == GoalText.gt_escape.lt(amp, lt, gt, c, r) : String}:
  match amp:
    case True{}:
      {==}
    case False{}:
      gtb.esc_gt(lt, gt, c, r)

def gtb.escape(s: String) -> {Gt.escape(s) == GoalText.gt_escape(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Gt.escape(t), GoalText.gt_escape(t), gtb.escape(t)) : {Gt.escape.lt(Char.is_eq(c, '&'), Char.is_eq(c, '<'), Char.is_eq(c, '>'), c, _) == GoalText.gt_escape.lt(Char.is_eq(c, '&'), Char.is_eq(c, '<'), Char.is_eq(c, '>'), c, GoalText.gt_escape(t)) : String}
      gtb.esc_lt(Char.is_eq(c, '&'), Char.is_eq(c, '<'), Char.is_eq(c, '>'), c, GoalText.gt_escape(t))

def gtb.objective(m: Maybe<&2, String>) -> {Gt.objective(m) == GoalText.gt_objective(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{o}:
      gtb.escape(o)

def gtb.budget_text(m: Maybe<&2, String>) -> {Gt.budget_text(m) == GoalText.gt_budget_text(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{b}:
      {==}

def gtb.left_text(m: Maybe<&2, String>, +used: String) -> {Gt.left_text(m, used) == GoalText.gt_left_text(m, used) : String}:
  match m:
    case None{}:
      {==}
    case Some{b}:
      gtb.left(b, used)

def gtb.continuation(g: Gt.Goal) -> {Gt.continuation(g) == GoalText.gt_continuation(g) : String}:
  match g:
    case Gt.Goal{+s, +o, +b, +u, t}:
      %Equal.sym(String, Gt.objective(o), GoalText.gt_objective(o), gtb.objective(o)) : {Gt.continuation.of(_, Gt.status_name(s), u, Gt.budget_text(b), Gt.left_text(b, u)) == GoalText.gt_continuation.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, GoalText.gt_budget_text(b), GoalText.gt_left_text(b, u)) : String}
      %Equal.sym(String, Gt.status_name(s), GoalText.gt_status_name(s), gtb.status_name(s)) : {Gt.continuation.of(GoalText.gt_objective(o), _, u, Gt.budget_text(b), Gt.left_text(b, u)) == GoalText.gt_continuation.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, GoalText.gt_budget_text(b), GoalText.gt_left_text(b, u)) : String}
      %Equal.sym(String, Gt.budget_text(b), GoalText.gt_budget_text(b), gtb.budget_text(b)) : {Gt.continuation.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, _, Gt.left_text(b, u)) == GoalText.gt_continuation.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, GoalText.gt_budget_text(b), GoalText.gt_left_text(b, u)) : String}
      %Equal.sym(String, Gt.left_text(b, u), GoalText.gt_left_text(b, u), gtb.left_text(b, u)) : {Gt.continuation.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, GoalText.gt_budget_text(b), _) == GoalText.gt_continuation.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, GoalText.gt_budget_text(b), GoalText.gt_left_text(b, u)) : String}
      {==}

def gtb.objective_updated(g: Gt.Goal) -> {Gt.objective_updated(g) == GoalText.gt_objective_updated(g) : String}:
  match g:
    case Gt.Goal{+s, +o, +b, +u, t}:
      %Equal.sym(String, Gt.objective(o), GoalText.gt_objective(o), gtb.objective(o)) : {Gt.objective_updated.of(_, Gt.status_name(s), u, Gt.budget_text(b), Gt.left_text(b, u)) == GoalText.gt_objective_updated.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, GoalText.gt_budget_text(b), GoalText.gt_left_text(b, u)) : String}
      %Equal.sym(String, Gt.status_name(s), GoalText.gt_status_name(s), gtb.status_name(s)) : {Gt.objective_updated.of(GoalText.gt_objective(o), _, u, Gt.budget_text(b), Gt.left_text(b, u)) == GoalText.gt_objective_updated.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, GoalText.gt_budget_text(b), GoalText.gt_left_text(b, u)) : String}
      %Equal.sym(String, Gt.budget_text(b), GoalText.gt_budget_text(b), gtb.budget_text(b)) : {Gt.objective_updated.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, _, Gt.left_text(b, u)) == GoalText.gt_objective_updated.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, GoalText.gt_budget_text(b), GoalText.gt_left_text(b, u)) : String}
      %Equal.sym(String, Gt.left_text(b, u), GoalText.gt_left_text(b, u), gtb.left_text(b, u)) : {Gt.objective_updated.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, GoalText.gt_budget_text(b), _) == GoalText.gt_objective_updated.of(GoalText.gt_objective(o), GoalText.gt_status_name(s), u, GoalText.gt_budget_text(b), GoalText.gt_left_text(b, u)) : String}
      {==}

def gtb.budget_limit(g: Gt.Goal) -> {Gt.budget_limit(g) == GoalText.gt_budget_limit(g) : String}:
  match g:
    case Gt.Goal{s, +o, +b, u, t}:
      %Equal.sym(String, Gt.objective(o), GoalText.gt_objective(o), gtb.objective(o)) : {Gt.budget_limit.of(_, u, Gt.budget_text(b), t) == GoalText.gt_budget_limit.of(GoalText.gt_objective(o), u, GoalText.gt_budget_text(b), t) : String}
      %Equal.sym(String, Gt.budget_text(b), GoalText.gt_budget_text(b), gtb.budget_text(b)) : {Gt.budget_limit.of(GoalText.gt_objective(o), u, _, t) == GoalText.gt_budget_limit.of(GoalText.gt_objective(o), u, GoalText.gt_budget_text(b), t) : String}
      {==}

def gtb.prompt(k: Gt.Prompt, g: Gt.Goal) -> {Gt.prompt(k, g) == GoalText.gt_prompt(k, g) : String}:
  match k:
    case Gt.KContinuation{}:
      gtb.continuation(g)
    case Gt.KBudgetLimit{}:
      gtb.budget_limit(g)
    case Gt.KObjectiveUpdated{}:
      gtb.objective_updated(g)

# Usage, report, host
# -------------------

def gtb.usage_seconds(zero: Bool, t: String) -> {Gt.usage.seconds(zero, t) == GoalText.gt_usage.seconds(zero, t) : Maybe<&2, String>}:
  match zero:
    case True{}:
      {==}
    case False{}:
      {==}

def gtb.usage(g: Gt.Goal) -> {Gt.usage(g) == GoalText.gt_usage(g) : Maybe<&2, String>}:
  match g:
    case Gt.Goal{s, o, b, u, +t}:
      match b:
        case None{}:
          gtb.usage_seconds(String.eq(t, "0"), t)
        case Some{x}:
          {==}

def gtb.parts(b: Maybe<&2, String>, u: String, zero: Bool, t: String) -> {Gt.report.parts(b, u, zero, t) == GoalText.gt_report.parts(b, u, zero, t) : List<&2, String>}:
  match b:
    case None{}:
      match zero:
        case True{}:
          {==}
        case False{}:
          {==}
    case Some{x}:
      match zero:
        case True{}:
          {==}
        case False{}:
          {==}

def gtb.report_of(ps: List<&2, String>) -> {Gt.report.of(ps) == GoalText.gt_report.of(ps) : Maybe<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      {==}

def gtb.report(g: Gt.Goal) -> {Gt.report(g) == GoalText.gt_report(g) : Maybe<&2, String>}:
  match g:
    case Gt.Goal{s, o, +b, +u, +t}:
      %Equal.sym(List<&2, String>, Gt.report.parts(b, u, String.eq(t, "0"), t), GoalText.gt_report.parts(b, u, String.eq(t, "0"), t), gtb.parts(b, u, String.eq(t, "0"), t)) : {Gt.report.of(_) == GoalText.gt_report.of(GoalText.gt_report.parts(b, u, String.eq(t, "0"), t)) : Maybe<&2, String>}
      gtb.report_of(GoalText.gt_report.parts(b, u, String.eq(t, "0"), t))

def gtb.remaining(b: Maybe<&2, String>, +u: String) -> {Gt.remaining(b, u) == GoalText.gt_remaining(b, u) : Maybe<&2, String>}:
  match b:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(String, Gt.left(x, u), GoalText.gt_left(x, u), gtb.left(x, u)) : {Some{_} == Some{GoalText.gt_left(x, u)} : Maybe<&2, String>}
      {==}

def gtb.complete(s: Gt.Status) -> {Gt.complete(s) == GoalText.gt_complete(s) : Bool}:
  match s:
    case Gt.SIdle{}:
      {==}
    case Gt.SActive{}:
      {==}
    case Gt.SPaused{}:
      {==}
    case Gt.SBudgetLimited{}:
      {==}
    case Gt.SComplete{}:
      {==}
    case Gt.SError{}:
      {==}

def gtb.idle(s: Gt.Status) -> {Gt.host.idle(s) == GoalText.gt_host.idle(s) : Bool}:
  match s:
    case Gt.SIdle{}:
      {==}
    case Gt.SActive{}:
      {==}
    case Gt.SPaused{}:
      {==}
    case Gt.SBudgetLimited{}:
      {==}
    case Gt.SComplete{}:
      {==}
    case Gt.SError{}:
      {==}

def gtb.host_report(due: Bool, g: Gt.Goal) -> {Gt.host.report(due, g) == GoalText.gt_host.report(due, g) : Maybe<&2, String>}:
  match due:
    case True{}:
      gtb.report(g)
    case False{}:
      {==}

def gtb.host_set(g: Gt.Goal, +ask: Bool) -> {Gt.host.set(g, ask) == GoalText.gt_host.set(g, ask) : Maybe<&2, Gt.Host>}:
  match g:
    case Gt.Goal{+s, +o, +b, +u, +t}:
      %Equal.sym(Maybe<&2, String>, Gt.remaining(b, u), GoalText.gt_remaining(b, u), gtb.remaining(b, u)) : {Some{Gt.Host{_, Gt.host.report(Bool.and(ask, Gt.complete(s)), Gt.Goal{s, o, b, u, t})}} == GoalText.gt_host.set(Gt.Goal{s, o, b, u, t}, ask) : Maybe<&2, Gt.Host>}
      %Equal.sym(Bool, Gt.complete(s), GoalText.gt_complete(s), gtb.complete(s)) : {Some{Gt.Host{GoalText.gt_remaining(b, u), Gt.host.report(Bool.and(ask, _), Gt.Goal{s, o, b, u, t})}} == GoalText.gt_host.set(Gt.Goal{s, o, b, u, t}, ask) : Maybe<&2, Gt.Host>}
      %Equal.sym(Maybe<&2, String>, Gt.host.report(Bool.and(ask, GoalText.gt_complete(s)), Gt.Goal{s, o, b, u, t}), GoalText.gt_host.report(Bool.and(ask, GoalText.gt_complete(s)), Gt.Goal{s, o, b, u, t}), gtb.host_report(Bool.and(ask, GoalText.gt_complete(s)), Gt.Goal{s, o, b, u, t})) : {Some{Gt.Host{GoalText.gt_remaining(b, u), _}} == GoalText.gt_host.set(Gt.Goal{s, o, b, u, t}, ask) : Maybe<&2, Gt.Host>}
      {==}

def gtb.host_of(idle: Bool, g: Gt.Goal, +ask: Bool) -> {Gt.host.of(idle, g, ask) == GoalText.gt_host.of(idle, g, ask) : Maybe<&2, Gt.Host>}:
  match idle:
    case True{}:
      {==}
    case False{}:
      gtb.host_set(g, ask)

def gtb.host(g: Gt.Goal, +ask: Bool) -> {Gt.host(g, ask) == GoalText.gt_host(g, ask) : Maybe<&2, Gt.Host>}:
  match g:
    case Gt.Goal{+s, o, b, u, t}:
      match o:
        case None{}:
          {==}
        case Some{x}:
          %Equal.sym(Bool, Gt.host.idle(s), GoalText.gt_host.idle(s), gtb.idle(s)) : {Gt.host.of(_, Gt.Goal{s, Some{x}, b, u, t}, ask) == GoalText.gt_host(Gt.Goal{s, Some{x}, b, u, t}, ask) : Maybe<&2, Gt.Host>}
          gtb.host_of(GoalText.gt_host.idle(s), Gt.Goal{s, Some{x}, b, u, t}, ask)
