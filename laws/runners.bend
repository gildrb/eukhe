# LAWS (G4): every runner of code goes through the gate. Each law is an
# open claim about the model in bend/runners.bend; PROOF.bend proves them
# (as Ru.<law>) with the lemmas of bend/proof_runners.bend.

import Base
import ../bend/runners.bend as Rn

# (G4) Every runner of code goes through the gate
# -----------------------------------------------
# docs/tools.md S7, the model in bend/runners.bend. `Rn.registry` is the
# registry a session installs (crates/eukhe-core/src/durable/registry.rs);
# the bridge test in crates/eukhe-core/src/durable/runner/tests.rs dumps
# the real registry and runs the `ipython` gate on the scenarios of
# bend/bridge_runners.bend, and both must print what the model prints.

# LAW: every tool of a session's registry (with or without chat memory)
# that runs code that may run a program is gated
law gate_covers_every_runner:
  for +chat: Bool
  for +i: Nat
  for +t: Rn.Tool
  for at: {List.get(&2, Rn.Tool, Rn.registry(chat), i) == Some{t} : Maybe<&2, Rn.Tool>}
  for runs: {Rn.runs(t) == True{} : Bool}
  {Rn.gated(t) == True{} : Bool}

# LAW: the `ipython` tool runs code that may run a program, and the gate
# covers each of its calls
law ipython_gated_each_call:
  for +chat: Bool
  {Rn.find(Rn.registry(chat), "ipython") == Some{Rn.Tool{"ipython", [Rn.exec()], Rn.EachCall{}}} : Maybe<&2, Rn.Tool>}

# LAW: a gated call runs only when its caps are within the auto set or the
# user approves it
law cell_runs_only_within_or_approved:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Rn.Asker
  for ran: {Rn.ran(Rn.cell(caps, auto, a)) == True{} : Bool}
  {Bool.or(Rn.within(caps, auto), Rn.Asker.yes(a)) == True{} : Bool}

# LAW: a call whose caps are within the auto set runs, unasked
law cell_within_runs_unasked:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for a: Rn.Asker
  for free: {Rn.within(caps, auto) == True{} : Bool}
  {Rn.cell(caps, auto, a) == Rn.Out{False{}, Rn.Ran{Rn.Auto{}}} : Rn.Out}

# LAW: a call outside the auto set that the user approves runs, asked
law cell_approved_runs:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for held: {Rn.within(caps, auto) == False{} : Bool}
  {Rn.cell(caps, auto, Rn.Says{True{}}) == Rn.Out{True{}, Rn.Ran{Rn.Approved{}}} : Rn.Out}

# LAW: a call outside the auto set without the user's approval (a denial,
# no answer, no client) does not run
law cell_no_yes_stops:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for +a: Rn.Asker
  for held: {Rn.within(caps, auto) == False{} : Bool}
  for no: {Rn.Asker.yes(a) == False{} : Bool}
  {Rn.ran(Rn.cell(caps, auto, a)) == False{} : Bool}

# LAW: code that may run a program is never within an auto set without
# `exec`
law cell_exec_asks:
  for +caps: List<&2, Nat>
  for +auto: List<&2, Nat>
  for has: {Rn.elem(caps, Rn.exec()) == True{} : Bool}
  for lacks: {Rn.elem(auto, Rn.exec()) == False{} : Bool}
  {Rn.within(caps, auto) == False{} : Bool}
