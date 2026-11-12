# eukhe: the proof of LAW wait_entry_priority
# A poll spelled from three Bools is read whole; for each state and each
# of the eight polls the stepper's state and reply compute to the table's
# (a tick of an open wait on each of the three shapes of its deadline).

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws

# the deadline's timer alone fired at an open wait
def pr.tick(left: Maybe<&2, Nat>) -> {FWt.step(FWt.Live{Wt.Open{left}}, WaitLaws.ww_spell(Wt.Polled{False{}, False{}, True{}})) == WaitLaws.ww_poll_spec(Wt.Open{left}, Wt.Polled{False{}, False{}, True{}}) : FWt.St & String}:
  match left:
    case None{}:
      {==}
    case Some{m}:
      match m:
        case 0n:
          {==}
        case 1n+q:
          {==}

def pr.over(a: Bool, c: Bool, l: Bool) -> {FWt.step(FWt.Live{Wt.Over{}}, WaitLaws.ww_spell(Wt.Polled{a, c, l})) == WaitLaws.ww_poll_spec(Wt.Over{}, Wt.Polled{a, c, l}) : FWt.St & String}:
  match a c l:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def pr.open(+left: Maybe<&2, Nat>, a: Bool, c: Bool, l: Bool) -> {FWt.step(FWt.Live{Wt.Open{left}}, WaitLaws.ww_spell(Wt.Polled{a, c, l})) == WaitLaws.ww_poll_spec(Wt.Open{left}, Wt.Polled{a, c, l}) : FWt.St & String}:
  match a c l:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      pr.tick(left)
    case False{} False{} False{}:
      {==}

def WaitLaws.wait_entry_priority(w, r):
  match w r:
    case Wt.Over{} Wt.Polled{a, c, l}:
      pr.over(a, c, l)
    case Wt.Open{left} Wt.Polled{a, c, l}:
      pr.open(left, a, c, l)
