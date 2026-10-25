# eukhe: the proof of LAW kept_once_in_order
#
# PROOF of LAW kept_once_in_order: by induction on the events, for every
# state: each event computes; what it releases, then the ids kept after it,
# are the ids kept before it, then the id it keeps or releases when it is a
# message to a paused tree (List.append is associative, kok_snoc); the rest
# follows by the induction hypothesis on the state after it.

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

# k, then id, then xs
def kok_snoc(k: List<&2, Nat>, -id: Nat, -xs: List<&2, Nat>) -> {List.append(&2, Nat, Wk.snoc(k, id), xs) == List.append(&2, Nat, k, id <> xs) : List<&2, Nat>}:
  LAWorker.wb_app_assoc(Nat, k, [id], xs)

def Worker.kept_once_in_order(h, s):
  match h s:
    case Nil{} Wk.St{m, p, +k, n}:
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, k, Nil{}), k, LAWorker.wb_app_nil(Nat, k))
    case Con{Wk.Pause{}, r} Wk.St{m, p, k, n}:
      Worker.kept_once_in_order(r, Wk.St{Wk.Paused{}, p, k, n})
    case Con{Wk.Resume{}, r} Wk.St{Wk.Run{}, p, k, n}:
      Worker.kept_once_in_order(r, Wk.St{Wk.Run{}, p, k, n})
    case Con{Wk.Resume{}, r} Wk.St{Wk.Paused{}, +p, +k, +n}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => List.append(&2, Nat, k, z), Worker.wk_out(r, Wk.St{Wk.Run{}, p, Nil{}, n}), Worker.wk_arrived(r, False{}), Worker.kept_once_in_order(r, Wk.St{Wk.Run{}, p, Nil{}, n}))
    case Con{Wk.Gate{g, i}, r} Wk.St{Wk.Run{}, p, k, n}:
      Worker.kept_once_in_order(r, Wk.St{Wk.Run{}, None{}, k, Wk.started(g, n)})
    case Con{Wk.Gate{g, i}, r} Wk.St{Wk.Paused{}, p, k, n}:
      Worker.kept_once_in_order(r, Wk.St{Wk.Paused{}, Some{i}, k, n})
    case Con{Wk.ToolDone{}, r} Wk.St{Wk.Run{}, p, k, n}:
      Worker.kept_once_in_order(r, Wk.St{Wk.Run{}, p, k, Wk.settled(n)})
    case Con{Wk.ToolDone{}, r} Wk.St{Wk.Paused{}, p, k, n}:
      Worker.kept_once_in_order(r, Wk.St{Wk.Paused{}, p, k, Wk.settled(n)})
    case Con{Wk.Msg{i, w}, r} Wk.St{Wk.Run{}, p, k, n}:
      Worker.kept_once_in_order(r, Wk.St{Wk.Run{}, p, k, n})
    case Con{Wk.Msg{+i, True{}}, r} Wk.St{Wk.Paused{}, +p, +k, +n}:
      +a = Worker.wk_arrived(r, False{})
      Equal.trans(List<&2, Nat>, List.append(&2, Nat, Wk.snoc(k, i), Worker.wk_out(r, Wk.St{Wk.Run{}, p, Nil{}, n})), List.append(&2, Nat, Wk.snoc(k, i), a), List.append(&2, Nat, k, i <> a),
        Equal.cong(List<&2, Nat>, List<&2, Nat>, z => List.append(&2, Nat, Wk.snoc(k, i), z), Worker.wk_out(r, Wk.St{Wk.Run{}, p, Nil{}, n}), a, Worker.kept_once_in_order(r, Wk.St{Wk.Run{}, p, Nil{}, n})),
        kok_snoc(k, i, a))
    case Con{Wk.Msg{+i, False{}}, r} Wk.St{Wk.Paused{}, +p, +k, +n}:
      +a = Worker.wk_arrived(r, True{})
      Equal.trans(List<&2, Nat>, Worker.wk_out(r, Wk.St{Wk.Paused{}, p, Wk.snoc(k, i), n}), List.append(&2, Nat, Wk.snoc(k, i), a), List.append(&2, Nat, k, i <> a),
        Worker.kept_once_in_order(r, Wk.St{Wk.Paused{}, p, Wk.snoc(k, i), n}),
        kok_snoc(k, i, a))
    case Con{Wk.End{}, r} Wk.St{Wk.Run{}, p, k, n}:
      Worker.kept_once_in_order(r, Wk.St{Wk.Run{}, None{}, k, 0n})
    case Con{Wk.End{}, r} Wk.St{Wk.Paused{}, p, k, n}:
      Worker.kept_once_in_order(r, Wk.St{Wk.Paused{}, None{}, k, 0n})
