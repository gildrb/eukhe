# eukhe: the proof of LAW wf_running_within_concurrency

import Base
import ../../bend/workflow.bend as W
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pw.give_size(p: W.Pool) -> {W.size(W.give(p)) == W.size(p) : Nat}:
  match p:
    case W.Pool{t, l}:
      match t:
        case 0n:
          {==}
        case 1n+s:
          Equal.sym(Nat, 1n+Nat.add(s, l), Nat.add(s, 1n+l), LA.pw.add_succ(s, l))

def pw.step_size(e: W.Ev, p: W.Pool) -> {W.size(W.step(e, p)) == W.size(p) : Nat}:
  match e:
    case W.Ask{}:
      LA.pw.take_size(p)
    case W.Settle{}:
      pw.give_size(p)

def pw.run_size(es: List<&2, W.Ev>, +p: W.Pool) -> {W.size(W.run(es, p)) == W.size(p) : Nat}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      Equal.trans(Nat, W.size(W.run(rest, W.step(e, p))), W.size(W.step(e, p)), W.size(p), pw.run_size(rest, W.step(e, p)), pw.step_size(e, p))

# (WF) Dynamic workflows

def Laws.wf_running_within_concurrency(cap, es):
  pw.run_size(es, W.pool(cap))
