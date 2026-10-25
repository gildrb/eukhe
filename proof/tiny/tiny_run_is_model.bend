# eukhe: the proof of LAW tiny_run_is_model
#
# PROOF: the run's first ping meets the worker's tag text a; the code
# compares it with the need's text b as the spec does (LA.te.same), which
# the premise names as the comparison of the tags t and m. On the same
# tag the run uses the connection at once: Joined, as the worker model's
# need gets. On another tag it shuts the worker down, launches, and its
# check meets its own tag (a text is the same as itself,
# LStaging.stg.same_refl): Replaced. With no worker it launches, and the
# check meets its own tag: Started.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/run.bend as TinyRun
import ../base/staging.bend as LStaging
import ./base.bend as LA

def tm.self(+b: String) -> {Tn.same(b, b) == True{} : Bool}:
  Equal.trans(Bool, Tn.same(b, b), LawsBase.text_same(b, b), True{}, LA.te.same(b, b), LStaging.stg.same_refl(b))

# the check after a start meets the need's own tag: the run uses it
def tm.check(+b: String, +g: Tn.Got) -> {Tn.step_run(Tn.Run{b, Tn.Checking{g}}, Tn.Pinged{Tn.Pong{b}}) == (Tn.Run{b, Tn.Over{}}, Tn.DoUse{g}) : Tn.Run & Tn.Do}:
  %Equal.sym(Bool, Tn.same(b, b), True{}, tm.self(b)) : {Tn.run.check(b, g, Tn.confirm.pong(_)) == (Tn.Run{b, Tn.Over{}}, Tn.DoUse{g}) : Tn.Run & Tn.Do}
  {==}

def tm.w(c: Bool, +b: String) -> {TinyRun.tr_used(Tn.DoPing{} <> TinyRun.tr_replies([Tn.ShutHeard{Tn.Bye{}}, Tn.Came{Tn.Bound{}}, Tn.Pinged{Tn.Pong{b}}], Tn.run.elect(b, Tn.elect.pong(c)))) == [Tn.need.g(c)] : List<&2, Tn.Got>}:
  match c:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Tn.Run & Tn.Do, Tn.step_run(Tn.Run{b, Tn.Checking{Tn.Replaced{}}}, Tn.Pinged{Tn.Pong{b}}), (Tn.Run{b, Tn.Over{}}, Tn.DoUse{Tn.Replaced{}}), tm.check(b, Tn.Replaced{})) : {TinyRun.tr_used(Tn.DoPing{} <> Tn.DoShutdown{} <> Tn.DoLaunch{} <> Tn.DoPing{} <> TinyRun.tr_replies(Nil{}, _)) == [Tn.Replaced{}] : List<&2, Tn.Got>}
      {==}

def tm.worker(+a: String, +b: String, +c: Bool, e: {Tn.same(a, b) == c : Bool}) -> {TinyRun.tr_used(TinyRun.tr_replies([Tn.Pinged{Tn.Pong{a}}, Tn.ShutHeard{Tn.Bye{}}, Tn.Came{Tn.Bound{}}, Tn.Pinged{Tn.Pong{b}}], Tn.need(b))) == [Tn.need.g(c)] : List<&2, Tn.Got>}:
  %Equal.sym(Bool, Tn.same(a, b), c, e) : {TinyRun.tr_used(Tn.DoPing{} <> TinyRun.tr_replies([Tn.ShutHeard{Tn.Bye{}}, Tn.Came{Tn.Bound{}}, Tn.Pinged{Tn.Pong{b}}], Tn.run.elect(b, Tn.elect.pong(_)))) == [Tn.need.g(c)] : List<&2, Tn.Got>}
  tm.w(c, b)

def tm.none(+b: String) -> {TinyRun.tr_used(TinyRun.tr_replies([Tn.Pinged{Tn.Missing{}}, Tn.Came{Tn.Bound{}}, Tn.Pinged{Tn.Pong{b}}], Tn.need(b))) == [Tn.Started{}] : List<&2, Tn.Got>}:
  %Equal.sym(Tn.Run & Tn.Do, Tn.step_run(Tn.Run{b, Tn.Checking{Tn.Started{}}}, Tn.Pinged{Tn.Pong{b}}), (Tn.Run{b, Tn.Over{}}, Tn.DoUse{Tn.Started{}}), tm.check(b, Tn.Started{})) : {TinyRun.tr_used(Tn.DoPing{} <> Tn.DoLaunch{} <> Tn.DoPing{} <> TinyRun.tr_replies(Nil{}, _)) == [Tn.Started{}] : List<&2, Tn.Got>}
  {==}

def TinyRun.tiny_run_is_model(o, t, q, m, a, b, named):
  (tm.worker(a, b, Nat.is_eq(t, m), Equal.trans(Bool, Tn.same(a, b), LawsBase.text_same(a, b), Nat.is_eq(t, m), LA.te.same(a, b), named)), tm.none(b))
