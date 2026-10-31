# eukhe: the proof of LAW finish_marks_passed

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as Autoresearch

def fmp.and_f(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fmp.and_t(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the shipped exit test is the law's
def fmp.ok(neg: Bool, +code: Nat, timeout: Bool) -> {ArP.ok_exit(neg, code, timeout) == Autoresearch.ar_exit_ok(neg, code, timeout) : Bool}:
  match neg:
    case True{}:
      {==}
    case False{}:
      match timeout:
        case True{}:
          fmp.and_f(Nat.is_eq(code, 0n))
        case False{}:
          fmp.and_t(Nat.is_eq(code, 0n))

def Autoresearch.finish_marks_passed(c, seg, mode, runs, id, kvs, neg, code, timeout):
  %fmp.ok(neg, code, timeout) : {ArP.step(ArS.St{c, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArS.Finish{neg, code, timeout}) == ArS.Took{ArS.St{c, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{_}}}}, ArS.Nothing{}, False{}} : ArS.Res}
  {==}
