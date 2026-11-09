# eukhe: the proof of LAW tiny_run_own_tag_used
#
# PROOF: the code compares the pong's tag with the run's char by char
# (Tn.same, the laws' text_same: LA.te.same), and a text is the same as
# itself (LStaging.stg.same_refl); on True the first ping joins and the
# check uses what the start got.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/elect.bend as TinyElect
import ../base/staging.bend as LStaging
import ./base.bend as LA

def tou.self(+m: String) -> {Tn.same(m, m) == True{} : Bool}:
  Equal.trans(Bool, Tn.same(m, m), LawsBase.text_same(m, m), True{}, LA.te.same(m, m), LStaging.stg.same_refl(m))

def tou.probing(+m: String) -> {Tn.step_run(Tn.Run{m, Tn.Probing{}}, Tn.Pinged{Tn.Pong{m}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoUse{Tn.Joined{}}) : Tn.Run & Tn.Do}:
  %Equal.sym(Bool, Tn.same(m, m), True{}, tou.self(m)) : {Tn.run.elect(m, Tn.elect.pong(_)) == (Tn.Run{m, Tn.Over{}}, Tn.DoUse{Tn.Joined{}}) : Tn.Run & Tn.Do}
  {==}

def tou.checking(+m: String, +g: Tn.Got) -> {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, Tn.Pinged{Tn.Pong{m}}) == (Tn.Run{m, Tn.Over{}}, Tn.DoUse{g}) : Tn.Run & Tn.Do}:
  %Equal.sym(Bool, Tn.same(m, m), True{}, tou.self(m)) : {Tn.run.check(m, g, Tn.confirm.pong(_)) == (Tn.Run{m, Tn.Over{}}, Tn.DoUse{g}) : Tn.Run & Tn.Do}
  {==}

def TinyElect.tiny_run_own_tag_used(m, g):
  (tou.probing(m), tou.checking(m, g))
