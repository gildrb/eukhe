# eukhe: the proof of LAW orphan_never_aborts_resumable

import Base
import ../../bend/orphan.bend as Or
import ../../LAWS.bend as Laws

# (D1) orphan_never_aborts_resumable
# ----------------------------------

def ps.exit_sound(work: Or.Work) -> Or.Sound(Or.Exited{Or.exit.done(Or.orphan_exit(work), work)}):
  match work:
    case Or.Idle{}:
      ({==}, {==})
    case Or.Ongoing{}:
      ({==}, {==})

def ps.check_put(due: Bool, +w: Or.W) -> Or.Sound(Or.check.put(due, w)):
  match due:
    case True{}:
      ps.exit_sound(Or.W.work(w))
    case False{}:
      Unit{}

def ps.check_sound(+window: Nat, +w: Or.W) -> Or.Sound(Or.check(window, w)):
  match w:
    case Or.W{r, q, c, a}:
      ps.check_put(Or.exit_due(window, a, Or.W.work(Or.W{r, q, c, a})), Or.W{r, q, c, a})

def ps.step_sound(+window: Nat, s: Or.St, +e: Or.Ev, ok: Or.Sound(s)) -> Or.Sound(Or.step(window, s, e)):
  match s:
    case Or.Live{w}:
      ps.check_sound(window, Or.apply(w, e))
    case Or.Exited{d}:
      ok

def ps.go_sound(+window: Nat, evs: List<&2, Or.Ev>, +s: Or.St, ok: Or.Sound(s)) -> Or.Sound(Or.go(window, evs, s)):
  match evs:
    case Nil{}:
      ok
    case +e <> rest:
      ps.go_sound(window, rest, Or.step(window, s, e), ps.step_sound(window, s, e, ok))

def ps.orphan_never_aborts_resumable(+window: Nat, +evs: List<&2, Or.Ev>) -> Or.Sound(Or.run(window, evs)):
  ps.go_sound(window, evs, Or.Live{Or.W.empty()}, Unit{})

def Laws.orphan_never_aborts_resumable(window, evs):
  ps.orphan_never_aborts_resumable(window, evs)
