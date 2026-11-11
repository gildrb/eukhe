# eukhe: the proof of LAW gate_held_denied_without_yes
# By induction on the steps before the held one: each runs unasked and
# takes no answer (LA.tgh.free); the held step, with no answer left or a
# no, is denied (LA.tgh.held, LA.tgh.deny).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pgd.nil(pre: List<&2, Tl.Step>, +s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, +free: {Tools.tg_all_free(pre, auto) == True{} : Bool}, held: {Tools.tg_free(s, auto) == False{} : Bool}) -> {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, Nil{}) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  match pre:
    case Nil{}:
      Equal.trans(Tl.Ran, Tl.exec(s <> post, auto, Nil{}), Tl.gate(False{}, s, Tl.Ran{Nil{}, Tl.Finished{}}), Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}}, LA.tgh.held(s, post, auto, Nil{}, held), LA.tgh.deny(s, Tl.Ran{Nil{}, Tl.Finished{}}))
    case +p <> +pr:
      Equal.trans(Tl.Ran, Tl.exec(p <> List.append(&2, Tl.Step, pr, s <> post), auto, Nil{}), Tl.ran.add(p, Tl.exec(List.append(&2, Tl.Step, pr, s <> post), auto, Nil{})), Tl.Ran{p <> pr, Tl.Denied{Tl.Step.id(s)}}, LA.tgh.free(p, List.append(&2, Tl.Step, pr, s <> post), auto, Nil{}, LA.tgh.and_l(Tools.tg_free(p, auto), Tools.tg_all_free(pr, auto), free)), Equal.cong(Tl.Ran, Tl.Ran, z => Tl.ran.add(p, z), Tl.exec(List.append(&2, Tl.Step, pr, s <> post), auto, Nil{}), Tl.Ran{pr, Tl.Denied{Tl.Step.id(s)}}, pgd.nil(pr, s, post, auto, LA.tgh.and_r(Tools.tg_free(p, auto), Tools.tg_all_free(pr, auto), free), held)))

def pgd.no(pre: List<&2, Tl.Step>, +s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, +ans: List<&2, Bool>, +free: {Tools.tg_all_free(pre, auto) == True{} : Bool}, held: {Tools.tg_free(s, auto) == False{} : Bool}) -> {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, False{} <> ans) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  match pre:
    case Nil{}:
      Equal.trans(Tl.Ran, Tl.exec(s <> post, auto, False{} <> ans), Tl.gate(False{}, s, Tl.exec(post, auto, ans)), Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}}, LA.tgh.held(s, post, auto, False{} <> ans, held), LA.tgh.deny(s, Tl.exec(post, auto, ans)))
    case +p <> +pr:
      Equal.trans(Tl.Ran, Tl.exec(p <> List.append(&2, Tl.Step, pr, s <> post), auto, False{} <> ans), Tl.ran.add(p, Tl.exec(List.append(&2, Tl.Step, pr, s <> post), auto, False{} <> ans)), Tl.Ran{p <> pr, Tl.Denied{Tl.Step.id(s)}}, LA.tgh.free(p, List.append(&2, Tl.Step, pr, s <> post), auto, False{} <> ans, LA.tgh.and_l(Tools.tg_free(p, auto), Tools.tg_all_free(pr, auto), free)), Equal.cong(Tl.Ran, Tl.Ran, z => Tl.ran.add(p, z), Tl.exec(List.append(&2, Tl.Step, pr, s <> post), auto, False{} <> ans), Tl.Ran{pr, Tl.Denied{Tl.Step.id(s)}}, pgd.no(pr, s, post, auto, ans, LA.tgh.and_r(Tools.tg_free(p, auto), Tools.tg_all_free(pr, auto), free), held)))

def Tools.gate_held_denied_without_yes(pre, s, post, auto, ans, free, held):
  (pgd.nil(pre, s, post, auto, free, held), pgd.no(pre, s, post, auto, ans, free, held))
