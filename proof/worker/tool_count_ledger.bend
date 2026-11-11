# eukhe: the proof of LAW tool_count_ledger
#
# PROOF of LAW tool_count_ledger: by the state and the event, each
# computes: a gate of a running tree starts the model's count of its kind,
# which is one more for kind 1 and the same for 0 and 2 or more (tcl_gate);
# a tool call's end settles to Base's n - 1 (tcl_done); the rest compute
# to the ledger's count as they stand.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def tcl_gate(g: Nat, -n: Nat) -> {Wk.started(g, n) == Nat.add(Worker.wk_one_if(Nat.is_eq(g, 1n)), n) : Nat}:
  match g:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+x:
      {==}

def tcl_sub0(q: Nat) -> {q == Nat.sub(q, 0n) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

def tcl_done(n: Nat) -> {Wk.settled(n) == Nat.sub(n, 1n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      tcl_sub0(q)

def Worker.tool_count_ledger(s, e):
  match s e:
    case Wk.St{m, p, k, n} Wk.Pause{}:
      {==}
    case Wk.St{Wk.Run{}, p, k, n} Wk.Resume{}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Resume{}:
      {==}
    case Wk.St{Wk.Run{}, p, k, n} Wk.Gate{g, i}:
      tcl_gate(g, n)
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Gate{g, i}:
      {==}
    case Wk.St{m, p, k, n} Wk.ToolDone{}:
      tcl_done(n)
    case Wk.St{Wk.Run{}, p, k, n} Wk.Msg{i, w}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, True{}}:
      {==}
    case Wk.St{Wk.Paused{}, p, k, n} Wk.Msg{i, False{}}:
      {==}
    case Wk.St{m, p, k, n} Wk.End{}:
      {==}
