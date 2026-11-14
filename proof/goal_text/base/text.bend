# eukhe: lemmas of area goal_text: the texts
#
# The spec helpers of laws/goal_text.bend that read one field (the status
# name, the objective shown, the budget shown, the tokens left shown) answer
# what the code's do, field by field (gtt.*); the completion report the
# code joins from its parts is the spec's text of each case (gth.*), by the
# associativity of String.append (gtt.assoc).

import Base
import ../../../bend/goal_text.bend as Gt
import ../../../laws/goal_text.bend as GoalText

def gtt.st(s: Gt.Status) -> {Gt.status_name(s) == GoalText.gt_status(s) : String}:
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

def gtt.obj(o: Maybe<&2, String>) -> {Gt.objective(o) == GoalText.gt_objective(o) : String}:
  match o:
    case None{}:
      {==}
    case Some{x}:
      {==}

def gtt.bud(b: Maybe<&2, String>) -> {Gt.budget_text(b) == GoalText.gt_budget(b) : String}:
  match b:
    case None{}:
      {==}
    case Some{x}:
      {==}

def gtt.rem(b: Maybe<&2, String>, +u: String) -> {Gt.left_text(b, u) == GoalText.gt_remaining(b, u) : String}:
  match b:
    case None{}:
      {==}
    case Some{x}:
      {==}

def gtt.left_of(b: Maybe<&2, String>, +u: String) -> {Gt.remaining(b, u) == GoalText.gt_left_of(b, u) : Maybe<&2, String>}:
  match b:
    case None{}:
      {==}
    case Some{x}:
      {==}

def gtt.assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, z => SCon{h, z}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), gtt.assoc(t, b, c))

# the tokens part alone, then "."
def gth.tok(u: String, +x: String) -> {String.append(String.append(u, String.append(" of ", String.append(x, ""))), ".") == String.append(u, String.append(" of ", String.append(x, "."))) : String}:
  match u:
    case SNil{}:
      Equal.cong(String, String, z => String.append(" of ", z), String.append(String.append(x, ""), "."), String.append(x, String.append("", ".")), gtt.assoc(x, "", "."))
    case SCon{h, t}:
      Equal.cong(String, String, z => SCon{h, z}, String.append(String.append(t, String.append(" of ", String.append(x, ""))), "."), String.append(t, String.append(" of ", String.append(x, "."))), gth.tok(t, x))

# the budget's digits, then the time part, then "."
def gth.both_x(x: String, +t: String) -> {String.append(String.append(String.append(x, ""), String.append("; time used: ", String.append(t, " seconds"))), ".") == String.append(x, String.append("; time used: ", String.append(t, " seconds."))) : String}:
  match x:
    case SNil{}:
      Equal.cong(String, String, z => String.append("; time used: ", z), String.append(String.append(t, " seconds"), "."), String.append(t, String.append(" seconds", ".")), gtt.assoc(t, " seconds", "."))
    case SCon{h, r}:
      Equal.cong(String, String, z => SCon{h, z}, String.append(String.append(String.append(r, ""), String.append("; time used: ", String.append(t, " seconds"))), "."), String.append(r, String.append("; time used: ", String.append(t, " seconds."))), gth.both_x(r, t))

# the tokens part, then the time part, then "."
def gth.both_u(u: String, +x: String, +t: String) -> {String.append(String.append(String.append(u, String.append(" of ", String.append(x, ""))), String.append("; time used: ", String.append(t, " seconds"))), ".") == String.append(u, String.append(" of ", String.append(x, String.append("; time used: ", String.append(t, " seconds."))))) : String}:
  match u:
    case SNil{}:
      Equal.cong(String, String, z => String.append(" of ", z), String.append(String.append(String.append(x, ""), String.append("; time used: ", String.append(t, " seconds"))), "."), String.append(x, String.append("; time used: ", String.append(t, " seconds."))), gth.both_x(x, t))
    case SCon{h, r}:
      Equal.cong(String, String, z => SCon{h, z}, String.append(String.append(String.append(r, String.append(" of ", String.append(x, ""))), String.append("; time used: ", String.append(t, " seconds"))), "."), String.append(r, String.append(" of ", String.append(x, String.append("; time used: ", String.append(t, " seconds."))))), gth.both_u(r, x, t))

# the report without a budget, for either answer z of "the seconds are 0"
def gth.rtime(-u: String, +t: String, z: Bool) -> {Gt.report.of(Gt.report.parts(None{}, u, z, t)) == GoalText.gt_report.time(z, t) : Maybe<&2, String>}:
  match z:
    case True{}:
      {==}
    case False{}:
      Equal.cong(String, Maybe<&2, String>, w => Some{String.append("Goal complete. Report final budget usage to the user: time used: ", w)}, String.append(String.append(t, " seconds"), "."), String.append(t, String.append(" seconds", ".")), gtt.assoc(t, " seconds", "."))

# the report with a budget, for either answer z of "the seconds are 0"
def gth.rboth(+u: String, +x: String, +t: String, z: Bool) -> {Gt.report.of(Gt.report.parts(Some{x}, u, z, t)) == GoalText.gt_report.both(z, u, x, t) : Maybe<&2, String>}:
  match z:
    case True{}:
      Equal.cong(String, Maybe<&2, String>, w => Some{String.append("Goal complete. Report final budget usage to the user: tokens used: ", w)}, String.append(String.append(u, String.append(" of ", String.append(x, ""))), "."), String.append(u, String.append(" of ", String.append(x, "."))), gth.tok(u, x))
    case False{}:
      Equal.cong(String, Maybe<&2, String>, w => Some{String.append("Goal complete. Report final budget usage to the user: tokens used: ", w)}, String.append(String.append(String.append(u, String.append(" of ", String.append(x, ""))), String.append("; time used: ", String.append(t, " seconds"))), "."), String.append(u, String.append(" of ", String.append(x, String.append("; time used: ", String.append(t, " seconds."))))), gth.both_u(u, x, t))

def gth.report(b: Maybe<&2, String>, +u: String, +t: String) -> {Gt.report.of(Gt.report.parts(b, u, String.eq(t, "0"), t)) == GoalText.gt_report(b, u, t) : Maybe<&2, String>}:
  match b:
    case None{}:
      gth.rtime(u, t, String.eq(t, "0"))
    case Some{x}:
      gth.rboth(u, x, t, String.eq(t, "0"))

def gth.rif(d: Bool, -s: Gt.Status, -o: Maybe<&2, String>, +b: Maybe<&2, String>, +u: String, +t: String) -> {Gt.host.report(d, Gt.Goal{s, o, b, u, t}) == GoalText.gt_report_if(d, b, u, t) : Maybe<&2, String>}:
  match d:
    case True{}:
      gth.report(b, u, t)
    case False{}:
      {==}

def gth.set(-s: Gt.Status, -x: String, +b: Maybe<&2, String>, +u: String, +t: String, +d: Bool) -> {Some{Gt.Host{Gt.remaining(b, u), Gt.host.report(d, Gt.Goal{s, Some{x}, b, u, t})}} == Some{Gt.Host{GoalText.gt_left_of(b, u), GoalText.gt_report_if(d, b, u, t)}} : Maybe<&2, Gt.Host>}:
  %gtt.left_of(b, u) : {Some{Gt.Host{Gt.remaining(b, u), Gt.host.report(d, Gt.Goal{s, Some{x}, b, u, t})}} == Some{Gt.Host{_, GoalText.gt_report_if(d, b, u, t)}} : Maybe<&2, Gt.Host>}
  %gth.rif(d, s, Some{x}, b, u, t) : {Some{Gt.Host{Gt.remaining(b, u), Gt.host.report(d, Gt.Goal{s, Some{x}, b, u, t})}} == Some{Gt.Host{Gt.remaining(b, u), _}} : Maybe<&2, Gt.Host>}
  {==}
