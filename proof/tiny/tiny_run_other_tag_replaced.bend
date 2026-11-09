# eukhe: the proof of LAW tiny_run_other_tag_replaced
#
# PROOF: the code's char by char comparison (Tn.same, the laws'
# text_same: LA.te.same) answers True only for equal texts
# (LStaging.stg.same_eq), which the premise excludes; so it answers
# False, and on False the first ping shuts the worker down and the check
# fails as mistagged.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/elect.bend as TinyElect
import ../base/staging.bend as LStaging
import ./base.bend as LA

# the code's comparison of two texts that differ is False
def tot.ne(b: Bool, +t: String, +m: String, eb: {Tn.same(t, m) == b : Bool}, ne: {t != m : String}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      +et = LStaging.stg.same_eq(t, m, Equal.trans(Bool, LawsBase.text_same(t, m), Tn.same(t, m), True{}, Equal.sym(Bool, Tn.same(t, m), LawsBase.text_same(t, m), LA.te.same(t, m)), eb))
      Empty.absurd({True{} == False{} : Bool}, ne(et))
    case False{}:
      {==}

def tot.probing(+m: String, +t: String, e: {Tn.same(t, m) == False{} : Bool}) -> {Tn.step_run(Tn.Run{m, Tn.Probing{}}, Tn.Pinged{Tn.Pong{t}}) == (Tn.Run{m, Tn.Shutting{}}, Tn.DoShutdown{}) : Tn.Run & Tn.Do}:
  %Equal.sym(Bool, Tn.same(t, m), False{}, e) : {Tn.run.elect(m, Tn.elect.pong(_)) == (Tn.Run{m, Tn.Shutting{}}, Tn.DoShutdown{}) : Tn.Run & Tn.Do}
  {==}

def tot.checking(+m: String, +t: String, +g: Tn.Got, e: {Tn.same(t, m) == False{} : Bool}) -> {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, Tn.Pinged{Tn.Pong{t}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyMistagged{}}) : Tn.Run & Tn.Do}:
  %Equal.sym(Bool, Tn.same(t, m), False{}, e) : {Tn.run.check(m, g, Tn.confirm.pong(_)) == (Tn.Run{m, Tn.Over{}}, Tn.DoFail{Tn.WhyMistagged{}}) : Tn.Run & Tn.Do}
  {==}

def TinyElect.tiny_run_other_tag_replaced(m, t, g, ne):
  +e = tot.ne(Tn.same(t, m), t, m, {==}, ne)
  (tot.probing(m, t, e), tot.checking(m, t, g, e))
