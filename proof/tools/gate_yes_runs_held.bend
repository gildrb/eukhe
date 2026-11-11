# eukhe: the proof of LAW gate_yes_runs_held
# By induction on the steps before the held one: each runs unasked and
# takes no answer (LA.tgh.free); the held step takes the yes and runs
# (LA.tgh.held), then the rest runs on the answers after it.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pgy.one(+s: Tl.Step, r: Tl.Ran) -> {Tl.ran.add(s, r) == Tools.tg_after([s], r) : Tl.Ran}:
  match r:
    case Tl.Ran{ss, e}:
      {==}

def pgy.cons(+p: Tl.Step, -xs: List<&2, Tl.Step>, r: Tl.Ran) -> {Tl.ran.add(p, Tools.tg_after(xs, r)) == Tools.tg_after(p <> xs, r) : Tl.Ran}:
  match r:
    case Tl.Ran{ss, e}:
      {==}

def pgy.yes(pre: List<&2, Tl.Step>, +s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, +ans: List<&2, Bool>, +free: {Tools.tg_all_free(pre, auto) == True{} : Bool}, held: {Tools.tg_free(s, auto) == False{} : Bool}) -> {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, True{} <> ans) == Tools.tg_after(List.append(&2, Tl.Step, pre, [s]), Tl.exec(post, auto, ans)) : Tl.Ran}:
  match pre:
    case Nil{}:
      Equal.trans(Tl.Ran, Tl.exec(s <> post, auto, True{} <> ans), Tl.ran.add(s, Tl.exec(post, auto, ans)), Tools.tg_after([s], Tl.exec(post, auto, ans)), LA.tgh.held(s, post, auto, True{} <> ans, held), pgy.one(s, Tl.exec(post, auto, ans)))
    case +p <> +pr:
      Equal.trans(Tl.Ran, Tl.exec(p <> List.append(&2, Tl.Step, pr, s <> post), auto, True{} <> ans), Tl.ran.add(p, Tl.exec(List.append(&2, Tl.Step, pr, s <> post), auto, True{} <> ans)), Tools.tg_after(p <> List.append(&2, Tl.Step, pr, [s]), Tl.exec(post, auto, ans)), LA.tgh.free(p, List.append(&2, Tl.Step, pr, s <> post), auto, True{} <> ans, LA.tgh.and_l(Tools.tg_free(p, auto), Tools.tg_all_free(pr, auto), free)), Equal.trans(Tl.Ran, Tl.ran.add(p, Tl.exec(List.append(&2, Tl.Step, pr, s <> post), auto, True{} <> ans)), Tl.ran.add(p, Tools.tg_after(List.append(&2, Tl.Step, pr, [s]), Tl.exec(post, auto, ans))), Tools.tg_after(p <> List.append(&2, Tl.Step, pr, [s]), Tl.exec(post, auto, ans)), Equal.cong(Tl.Ran, Tl.Ran, z => Tl.ran.add(p, z), Tl.exec(List.append(&2, Tl.Step, pr, s <> post), auto, True{} <> ans), Tools.tg_after(List.append(&2, Tl.Step, pr, [s]), Tl.exec(post, auto, ans)), pgy.yes(pr, s, post, auto, ans, LA.tgh.and_r(Tools.tg_free(p, auto), Tools.tg_all_free(pr, auto), free), held)), pgy.cons(p, List.append(&2, Tl.Step, pr, [s]), Tl.exec(post, auto, ans))))

def Tools.gate_yes_runs_held(pre, s, post, auto, ans, free, held):
  pgy.yes(pre, s, post, auto, ans, free, held)
