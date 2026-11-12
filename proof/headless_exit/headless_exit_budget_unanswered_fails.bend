# eukhe: the proof of LAW headless_exit_budget_unanswered_fails
#
# PROOF: without the final answer from the reserve each of the three is a
# failure of its own: the wait at the deadline after the command
# (hxu.deadline), a run the budget refused below the wait
# (hx.facts_fail), a terminal entry the budget refused below the run
# (hx.facts_fail, hx.run_fails); each code is 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def hxu.deadline(cf: Bool, -r: Hx.Run, -p: Hx.Primary, -c: Bool, -a: Bool) -> {HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, Hx.BudgetDeadline{}, r, p, c, a, False{}})) == 1n : Nat}:
  match cf:
    case True{}:
      {==}
    case False{}:
      {==}

def HeadlessExit.headless_exit_budget_unanswered_fails(cf, w, r, p, c, a):
  %Equal.sym(Nat, HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, Hx.BudgetDeadline{}, r, p, c, a, False{}})), 1n, hxu.deadline(cf, r, p, c, a)) : {[_, HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.BudgetRefused{}}, p, c, a, False{}})), HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, r, Hx.PBudgetRefused{}, c, a, False{}}))] == [1n, 1n, 1n] : List<&2, Nat>}
  %Equal.sym(Nat, HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.BudgetRefused{}}, p, c, a, False{}})), 1n, LAHeadlessExit.hx.facts_fail(cf, w, Hx.Unanswered{Hx.BudgetRefused{}}, p, c, a, False{}, {==})) : {[1n, _, HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, r, Hx.PBudgetRefused{}, c, a, False{}}))] == [1n, 1n, 1n] : List<&2, Nat>}
  %Equal.sym(Nat, HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, r, Hx.PBudgetRefused{}, c, a, False{}})), 1n, LAHeadlessExit.hx.facts_fail(cf, w, r, Hx.PBudgetRefused{}, c, a, False{}, LAHeadlessExit.hx.run_fails(r, Hx.PBudgetRefused{}, c, a, False{}, {==}))) : {[1n, 1n, _] == [1n, 1n, 1n] : List<&2, Nat>}
  {==}
