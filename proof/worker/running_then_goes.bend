# eukhe: the proof of LAW running_then_goes
#
# PROOF of LAW running_then_goes: every event that is not a pause keeps a
# running tree running (rtg_step), so it runs after the events with no
# pause (rtg_after, by induction on them); a gate of a running state goes
# (rtg_gate).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

# the events that are not a pause
def rtg_calm(e: Wk.Ev) -> Bool:
  match e:
    case Wk.Pause{}:
      False{}
    case Wk.Resume{}:
      True{}
    case Wk.Gate{g, i}:
      True{}
    case Wk.ToolDone{}:
      True{}
    case Wk.Msg{i, w}:
      True{}
    case Wk.End{}:
      True{}

def rtg_step(m: Wk.Mode, -p: Maybe<&2, Nat>, -k: List<&2, Nat>, -n: Nat, e: Wk.Ev, hm: {Worker.wk_paused(Wk.St{m, p, k, n}) == False{} : Bool}, q: {rtg_calm(e) == True{} : Bool}) ->
  {Worker.wk_paused(Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, e))) == False{} : Bool}:
  match m e:
    case Wk.Paused{} _:
      LAWorker.wb_absurd_tf({Worker.wk_paused(Worker.wk_state(Wk.step(Wk.St{Wk.Paused{}, p, k, n}, e))) == False{} : Bool}, hm)
    case Wk.Run{} Wk.Pause{}:
      LAWorker.wb_absurd_ft({Worker.wk_paused(Worker.wk_state(Wk.step(Wk.St{Wk.Run{}, p, k, n}, Wk.Pause{}))) == False{} : Bool}, q)
    case Wk.Run{} Wk.Resume{}:
      {==}
    case Wk.Run{} Wk.Gate{g, i}:
      {==}
    case Wk.Run{} Wk.ToolDone{}:
      {==}
    case Wk.Run{} Wk.Msg{i, w}:
      {==}
    case Wk.Run{} Wk.End{}:
      {==}

# a running tree stays running over events with no pause
def rtg_after(h: List<&2, Wk.Ev>, s: Wk.St, q: {Worker.wk_no_pause(h) == True{} : Bool}, hm: {Worker.wk_paused(s) == False{} : Bool}) ->
  {Worker.wk_paused(Worker.wk_after(h, s)) == False{} : Bool}:
  match h s:
    case Nil{} _:
      hm
    case Con{Wk.Pause{}, r} Wk.St{m, p, k, n}:
      LAWorker.wb_absurd_ft({Worker.wk_paused(Worker.wk_after(Wk.Pause{} <> r, Wk.St{m, p, k, n})) == False{} : Bool}, q)
    case Con{Wk.Resume{}, r} Wk.St{+m, +p, +k, +n}:
      rtg_after(r, Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, Wk.Resume{})), q, rtg_step(m, p, k, n, Wk.Resume{}, hm, {==}))
    case Con{Wk.Gate{+g, +i}, r} Wk.St{+m, +p, +k, +n}:
      rtg_after(r, Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, Wk.Gate{g, i})), q, rtg_step(m, p, k, n, Wk.Gate{g, i}, hm, {==}))
    case Con{Wk.ToolDone{}, r} Wk.St{+m, +p, +k, +n}:
      rtg_after(r, Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, Wk.ToolDone{})), q, rtg_step(m, p, k, n, Wk.ToolDone{}, hm, {==}))
    case Con{Wk.Msg{+i, +w}, r} Wk.St{+m, +p, +k, +n}:
      rtg_after(r, Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, Wk.Msg{i, w})), q, rtg_step(m, p, k, n, Wk.Msg{i, w}, hm, {==}))
    case Con{Wk.End{}, r} Wk.St{+m, +p, +k, +n}:
      rtg_after(r, Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, Wk.End{})), q, rtg_step(m, p, k, n, Wk.End{}, hm, {==}))

# a gate of a running state goes
def rtg_gate(x: Wk.St, -kind: Nat, -id: Nat, hm: {Worker.wk_paused(x) == False{} : Bool}) ->
  {Worker.wk_verdict(Wk.step(x, Wk.Gate{kind, id})) == Wk.Go{} : Wk.Verdict}:
  match x:
    case Wk.St{m, p, k, n}:
      match m:
        case Wk.Run{}:
          {==}
        case Wk.Paused{}:
          LAWorker.wb_absurd_tf({Worker.wk_verdict(Wk.step(Wk.St{Wk.Paused{}, p, k, n}, Wk.Gate{kind, id})) == Wk.Go{} : Wk.Verdict}, hm)

def Worker.running_then_goes(s, run, h, calm, kind, id):
  rtg_gate(Worker.wk_after(h, s), kind, id, rtg_after(h, s, calm, run))
