# eukhe: the laws of area runners

import Base
import ../bend/runners.bend as Ru

# ---- runners ----

# LAWS (G4): every runner of code goes through the gate. Each law is an
# open claim about the model in bend/runners.bend; PROOF.bend proves them
# (as Runners.<law>) with the lemmas of proof/runners/.

# (G4) Every runner of code goes through the gate
# -----------------------------------------------
# docs/tools.md S7, the model in bend/runners.bend. `Rn.registry` is the
# registry a session installs (crates/eukhe-core/src/durable/registry.rs);
# the bridge test in crates/eukhe-core/src/durable/runner/tests.rs dumps
# the real registry and runs the `ipython` gate on the scenarios of
# bridge/bridge_runners.bend, and both must print what the model prints.

# LAW gate_covers_every_runner: every tool of a session's registry (with or without chat memory)
# that runs code that may run a program is gated
law gate_covers_every_runner:
  for +chat: Bool
  for +i: Nat
  for +t: Ru.Tool
  for at: {List.get(&2, Ru.Tool, Ru.registry(chat), i) == Some{t} : Maybe<&2, Ru.Tool>}
  for runs: {Ru.runs(t) == True{} : Bool}
  {Ru.gated(t) == True{} : Bool}

# LAW ipython_gated_each_call: the `ipython` tool runs code that may run a program, and the gate
# covers each of its calls
law ipython_gated_each_call:
  for +chat: Bool
  {Ru.find(Ru.registry(chat), "ipython") == Some{Ru.Tool{"ipython", [Ru.exec()], Ru.EachCall{}}} : Maybe<&2, Ru.Tool>}

# LAW cell_runs_only_within_or_approved: a gated call runs only when its caps are within the auto set or the
# user approves it
law cell_runs_only_within_or_approved:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Ru.Asker
  for ran: {Ru.ran(Ru.cell(caps, auto, a)) == True{} : Bool}
  {Bool.or(Ru.within(caps, auto), Ru.Asker.yes(a)) == True{} : Bool}

# LAW cell_within_runs_unasked: a call whose caps are within the auto set runs, unasked
law cell_within_runs_unasked:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for a: Ru.Asker
  for free: {Ru.within(caps, auto) == True{} : Bool}
  {Ru.cell(caps, auto, a) == Ru.Out{False{}, Ru.Ran{Ru.Auto{}}} : Ru.Out}

# LAW cell_approved_runs: a call outside the auto set that the user approves runs, asked
law cell_approved_runs:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for held: {Ru.within(caps, auto) == False{} : Bool}
  {Ru.cell(caps, auto, Ru.Says{True{}}) == Ru.Out{True{}, Ru.Ran{Ru.Approved{}}} : Ru.Out}

# LAW cell_no_yes_stops: a call outside the auto set without the user's approval (a denial,
# no answer, no client) does not run
law cell_no_yes_stops:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Ru.Asker
  for held: {Ru.within(caps, auto) == False{} : Bool}
  for no: {Ru.Asker.yes(a) == False{} : Bool}
  {Ru.ran(Ru.cell(caps, auto, a)) == False{} : Bool}

# LAW cell_exec_asks: code that may run a program is never within an auto set without
# `exec`
law cell_exec_asks:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for has: {Ru.elem(caps, Ru.exec()) == True{} : Bool}
  for lacks: {Ru.elem(auto, Ru.exec()) == False{} : Bool}
  {Ru.within(caps, auto) == False{} : Bool}
