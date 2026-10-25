# eukhe: the proof of LAW pause_then_holds
#
# PROOF of LAW pause_then_holds: after the pause the tree is paused; every
# event that is not a resume or a waking message keeps it paused (pth_step),
# so it is paused after the quiet events (pth_after, by induction on them);
# a gate of a paused state holds and parks (pth_gate).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

# the events that keep a paused tree paused
def pth_quiet(e: Wk.Ev) -> Bool:
  match e:
    case Wk.Resume{}:
      False{}
    case Wk.Msg{i, w}:
      Bool.not(w)
    case Wk.Pause{}:
      True{}
    case Wk.Gate{g, i}:
      True{}
    case Wk.ToolDone{}:
      True{}
    case Wk.End{}:
      True{}

def pth_step(m: Wk.Mode, -p: Maybe<&2, Nat>, -k: List<&2, Nat>, -n: Nat, e: Wk.Ev, hm: {Worker.wk_paused(Wk.St{m, p, k, n}) == True{} : Bool}, q: {pth_quiet(e) == True{} : Bool}) ->
  {Worker.wk_paused(Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, e))) == True{} : Bool}:
  match m e:
    case Wk.Run{} _:
      LAWorker.wb_absurd_ft({Worker.wk_paused(Worker.wk_state(Wk.step(Wk.St{Wk.Run{}, p, k, n}, e))) == True{} : Bool}, hm)
    case Wk.Paused{} Wk.Pause{}:
      {==}
    case Wk.Paused{} Wk.Resume{}:
      LAWorker.wb_absurd_ft({Worker.wk_paused(Worker.wk_state(Wk.step(Wk.St{Wk.Paused{}, p, k, n}, Wk.Resume{}))) == True{} : Bool}, q)
    case Wk.Paused{} Wk.Gate{g, i}:
      {==}
    case Wk.Paused{} Wk.ToolDone{}:
      {==}
    case Wk.Paused{} Wk.Msg{i, w}:
      match w:
        case True{}:
          LAWorker.wb_absurd_ft({Worker.wk_paused(Worker.wk_state(Wk.step(Wk.St{Wk.Paused{}, p, k, n}, Wk.Msg{i, True{}}))) == True{} : Bool}, q)
        case False{}:
          {==}
    case Wk.Paused{} Wk.End{}:
      {==}

# a paused tree stays paused over quiet events
def pth_after(h: List<&2, Wk.Ev>, s: Wk.St, q: {Worker.wk_quiet(h) == True{} : Bool}, hm: {Worker.wk_paused(s) == True{} : Bool}) ->
  {Worker.wk_paused(Worker.wk_after(h, s)) == True{} : Bool}:
  match h s:
    case Nil{} _:
      hm
    case Con{Wk.Resume{}, r} Wk.St{m, p, k, n}:
      LAWorker.wb_absurd_ft({Worker.wk_paused(Worker.wk_after(Wk.Resume{} <> r, Wk.St{m, p, k, n})) == True{} : Bool}, q)
    case Con{Wk.Msg{i, True{}}, r} Wk.St{m, p, k, n}:
      LAWorker.wb_absurd_ft({Worker.wk_paused(Worker.wk_after(Wk.Msg{i, True{}} <> r, Wk.St{m, p, k, n})) == True{} : Bool}, q)
    case Con{Wk.Msg{+i, False{}}, r} Wk.St{+m, +p, +k, +n}:
      pth_after(r, Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, Wk.Msg{i, False{}})), q, pth_step(m, p, k, n, Wk.Msg{i, False{}}, hm, {==}))
    case Con{Wk.Pause{}, r} Wk.St{+m, +p, +k, +n}:
      pth_after(r, Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, Wk.Pause{})), q, pth_step(m, p, k, n, Wk.Pause{}, hm, {==}))
    case Con{Wk.Gate{+g, +i}, r} Wk.St{+m, +p, +k, +n}:
      pth_after(r, Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, Wk.Gate{g, i})), q, pth_step(m, p, k, n, Wk.Gate{g, i}, hm, {==}))
    case Con{Wk.ToolDone{}, r} Wk.St{+m, +p, +k, +n}:
      pth_after(r, Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, Wk.ToolDone{})), q, pth_step(m, p, k, n, Wk.ToolDone{}, hm, {==}))
    case Con{Wk.End{}, r} Wk.St{+m, +p, +k, +n}:
      pth_after(r, Worker.wk_state(Wk.step(Wk.St{m, p, k, n}, Wk.End{})), q, pth_step(m, p, k, n, Wk.End{}, hm, {==}))

# a gate of a paused state holds and parks
def pth_gate(x: Wk.St, -kind: Nat, -id: Nat, hm: {Worker.wk_paused(x) == True{} : Bool}) ->
  {Wk.step(x, Wk.Gate{kind, id}) == (Worker.wk_held(x, id), Wk.Hold{}) : Wk.St & Wk.Verdict}:
  match x:
    case Wk.St{m, p, k, n}:
      match m:
        case Wk.Run{}:
          LAWorker.wb_absurd_ft({Wk.step(Wk.St{Wk.Run{}, p, k, n}, Wk.Gate{kind, id}) == (Worker.wk_held(Wk.St{Wk.Run{}, p, k, n}, id), Wk.Hold{}) : Wk.St & Wk.Verdict}, hm)
        case Wk.Paused{}:
          {==}

# a pause pauses any state
def pth_pause(s: Wk.St) -> {Worker.wk_paused(Worker.wk_state(Wk.step(s, Wk.Pause{}))) == True{} : Bool}:
  match s:
    case Wk.St{m, p, k, n}:
      {==}

def Worker.pause_then_holds(s, h, quiet, kind, id):
  +x = Worker.wk_after(h, Worker.wk_state(Wk.step(s, Wk.Pause{})))
  pth_gate(x, kind, id, pth_after(h, Worker.wk_state(Wk.step(s, Wk.Pause{})), quiet, pth_pause(s)))
