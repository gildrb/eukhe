# eukhe: the proof of LAW paused_keeps_arrivals
#
# PROOF of LAW paused_keeps_arrivals: a pause keeps what was kept and
# pauses the tree; then, by induction on the quiet events, for every paused
# state (pka): a pause, a gate, a tool's end and the run's end keep the
# tree paused and the kept ids as they are; a report keeps the tree paused
# and puts its id last (List.append is associative); a resume and a waking
# message contradict the premise; a running state contradicts the mode.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def pka_goal(h: List<&2, Wk.Ev>, x: Wk.St) -> Type:
  {Worker.wk_kept(Worker.wk_after(h, x)) == List.append(&2, Nat, Worker.wk_kept(x), Worker.wk_msg_ids(h)) : List<&2, Nat>}

def pka(h: List<&2, Wk.Ev>, x: Wk.St, q: {Worker.wk_quiet(h) == True{} : Bool}, hm: {Worker.wk_paused(x) == True{} : Bool}) -> pka_goal(h, x):
  match h x:
    case Nil{} Wk.St{m, p, +k, n}:
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, k, Nil{}), k, LAWorker.wb_app_nil(Nat, k))
    case Con{e, r} Wk.St{Wk.Run{}, p, k, n}:
      LAWorker.wb_absurd_ft(pka_goal(e <> r, Wk.St{Wk.Run{}, p, k, n}), hm)
    case Con{Wk.Pause{}, r} Wk.St{Wk.Paused{}, +p, +k, +n}:
      pka(r, Wk.St{Wk.Paused{}, p, k, n}, q, {==})
    case Con{Wk.Resume{}, r} Wk.St{Wk.Paused{}, p, k, n}:
      LAWorker.wb_absurd_ft(pka_goal(Wk.Resume{} <> r, Wk.St{Wk.Paused{}, p, k, n}), q)
    case Con{Wk.Gate{g, +i}, r} Wk.St{Wk.Paused{}, p, +k, +n}:
      pka(r, Wk.St{Wk.Paused{}, Some{i}, k, n}, q, {==})
    case Con{Wk.ToolDone{}, r} Wk.St{Wk.Paused{}, +p, +k, +n}:
      pka(r, Wk.St{Wk.Paused{}, p, k, Wk.settled(n)}, q, {==})
    case Con{Wk.Msg{i, True{}}, r} Wk.St{Wk.Paused{}, p, k, n}:
      LAWorker.wb_absurd_ft(pka_goal(Wk.Msg{i, True{}} <> r, Wk.St{Wk.Paused{}, p, k, n}), q)
    case Con{Wk.Msg{+i, False{}}, +r} Wk.St{Wk.Paused{}, +p, +k, +n}:
      +a = Worker.wk_msg_ids(r)
      Equal.trans(List<&2, Nat>, Worker.wk_kept(Worker.wk_after(r, Wk.St{Wk.Paused{}, p, Wk.snoc(k, i), n})), List.append(&2, Nat, Wk.snoc(k, i), a), List.append(&2, Nat, k, i <> a),
        pka(r, Wk.St{Wk.Paused{}, p, Wk.snoc(k, i), n}, q, {==}),
        LAWorker.wb_app_assoc(Nat, k, [i], a))
    case Con{Wk.End{}, r} Wk.St{Wk.Paused{}, +p, +k, +n}:
      pka(r, Wk.St{Wk.Paused{}, None{}, k, 0n}, q, {==})

def Worker.paused_keeps_arrivals(s, h, quiet):
  match s:
    case Wk.St{m, p, k, n}:
      pka(h, Wk.St{Wk.Paused{}, p, k, n}, quiet, {==})
