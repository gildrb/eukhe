# eukhe: the proof of LAW headless_exit_budget_keeps_other_failures
#
# PROOF: the delivered final answer excuses only the facts a used-up
# budget leaves: a model error is a run failure (hx.facts_fail), a
# give-up and a failed command are causes above the run (hxk.gave_up, a
# computation), a failed compaction fails below every excused fact
# (hx.facts_fail, hx.run_fails, hx.comp_fails); each code is 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def hxk.gave_up(cf: Bool, -r: Hx.Run, -p: Hx.Primary, -c: Bool, -a: Bool) -> {HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, Hx.GaveUp{}, r, p, c, a, True{}})) == 1n : Nat}:
  match cf:
    case True{}:
      {==}
    case False{}:
      {==}

def HeadlessExit.headless_exit_budget_keeps_other_failures(cf, w, r, p, c, a):
  %Equal.sym(Nat, HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, Hx.Unanswered{Hx.ModelError{}}, p, c, a, True{}})), 1n, LAHeadlessExit.hx.facts_fail(cf, w, Hx.Unanswered{Hx.ModelError{}}, p, c, a, True{}, {==})) : {[_, HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, Hx.GaveUp{}, r, p, c, a, True{}})), HeadlessExit.code_of(Hx.decide(Hx.Facts{True{}, w, r, p, c, a, True{}})), HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, r, p, True{}, a, True{}}))] == [1n, 1n, 1n, 1n] : List<&2, Nat>}
  %Equal.sym(Nat, HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, Hx.GaveUp{}, r, p, c, a, True{}})), 1n, hxk.gave_up(cf, r, p, c, a)) : {[1n, _, HeadlessExit.code_of(Hx.decide(Hx.Facts{True{}, w, r, p, c, a, True{}})), HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, r, p, True{}, a, True{}}))] == [1n, 1n, 1n, 1n] : List<&2, Nat>}
  %Equal.sym(Nat, HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, r, p, True{}, a, True{}})), 1n, LAHeadlessExit.hx.facts_fail(cf, w, r, p, True{}, a, True{}, LAHeadlessExit.hx.run_fails(r, p, True{}, a, True{}, LAHeadlessExit.hx.comp_fails(p, a, True{})))) : {[1n, 1n, HeadlessExit.code_of(Hx.decide(Hx.Facts{True{}, w, r, p, c, a, True{}})), _] == [1n, 1n, 1n, 1n] : List<&2, Nat>}
  {==}
