# eukhe: the proof of LAW once_tool_gate_agrees
#
# PROOF: both rules compute on each stored and current policy.

import Base
import ../../bend/once.bend as O
import ../../bend/tool_call.bend as Tc
import ../../laws/once.bend as Once

def og.rerun(stored: Tc.Replay, now: Tc.Replay, -again: Nat) -> {Once.on_go(True{}, O.recover(O.Running{again}, O.Dark{}, O.Resume{}, Once.on_both(stored, now))) == Tc.gate(Tc.Recover{True{}, stored, Tc.Offered{now}}) : Tc.Go}:
  match stored:
    case Tc.Safe{}:
      match now:
        case Tc.Safe{}:
          {==}
        case Tc.Unsafe{}:
          {==}
    case Tc.Unsafe{}:
      match now:
        case Tc.Safe{}:
          {==}
        case Tc.Unsafe{}:
          {==}

def og.gone(stored: Tc.Replay, -again: Nat) -> {Once.on_go(True{}, O.recover(O.Running{again}, O.Dark{}, O.Resume{}, O.Never{})) == Tc.gate(Tc.Recover{True{}, stored, Tc.Gone{}}) : Tc.Go}:
  match stored:
    case Tc.Safe{}:
      {==}
    case Tc.Unsafe{}:
      {==}

def og.all(+stored: Tc.Replay, +now: Tc.Replay, -s: O.Seen, -p: O.Policy, -again: Nat) -> ({Once.on_go(True{}, O.recover(O.Running{again}, O.Dark{}, O.Resume{}, Once.on_both(stored, now))) == Tc.gate(Tc.Recover{True{}, stored, Tc.Offered{now}}) : Tc.Go} & {Once.on_go(True{}, O.recover(O.Running{again}, O.Dark{}, O.Resume{}, O.Never{})) == Tc.gate(Tc.Recover{True{}, stored, Tc.Gone{}}) : Tc.Go} & {Once.on_go(True{}, O.recover(O.Running{again}, O.Dark{}, O.Stop{}, p)) == Tc.gate(Tc.Stop{True{}, True{}, True{}}) : Tc.Go} & {Once.on_go(False{}, O.recover(O.Pending{}, s, O.Stop{}, p)) == Tc.gate(Tc.Stop{True{}, True{}, False{}}) : Tc.Go} & {Once.on_go(False{}, O.recover(O.Pending{}, s, O.Resume{}, p)) == Tc.gate(Tc.Enter{True{}, Tc.Offered{now}}) : Tc.Go}):
  (og.rerun(stored, now, again), (og.gone(stored, again), ({==}, ({==}, {==}))))

def Once.once_tool_gate_agrees(stored, now, s, p, again):
  og.all(stored, now, s, p, again)
