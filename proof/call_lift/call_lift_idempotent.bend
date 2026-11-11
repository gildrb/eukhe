# eukhe: the proof of LAW call_lift_idempotent
#
# PROOF: both lifts are the proof model's (clm.refines, ./base/refines.bend); by cases on the family's current rev, whether the call is at it and whether its chain arrives: an unknown, current or stranded call is applied as stored, so its second lift answers as the first (the equations of each case rewrite it back); a lifted call is applied at the current rev, so its second lift is current by String.eq reflexivity (clm.str_refl).

import Base
import ../../bend/call_lift.bend as Cl
import ./base/model.bend as Sp
import ../../laws/call_lift.bend as CallLift
import ./base/string.bend as LCallLiftString
import ./base/refines.bend as LCallLiftRefines

# a lifted call, applied, lifts as current
def clm.id.st(st: Cl.St, +t: List<&2, Cl.Fam>, +f: String, r: String, ks: List<&2, String>, +cur: String, e: {Some{cur} == Sp.current(t, f) : Maybe<&2, String>}) -> {Sp.lift_spec(t, CallLift.applied.l(f, r, ks, Sp.lift_spec.done(cur, st))) == CallLift.settled(Sp.lift_spec.done(cur, st)) : Cl.Lift}:
  match st:
    case Cl.St{+a, rs}:
      %e : {Sp.lift_spec.cur(cur, CallLift.keys_of(a), _, Sp.steps_of(t, f)) == Cl.Current{} : Cl.Lift}
      %LCallLiftString.clm.str_refl_sym(cur) : {Sp.lift_spec.at(_, cur, CallLift.keys_of(a), Sp.chain(List.length(&2, Cl.Step, Sp.steps_of(t, f)), Sp.steps_of(t, f), cur, Sp.next(Sp.steps_of(t, f), cur))) == Cl.Current{} : Cl.Lift}
      {==}

# a stranded call, applied as stored, is stranded again
def clm.id.none(+t: List<&2, Cl.Fam>, +f: String, +r: String, +ks: List<&2, String>, +cur: String, e: {Some{cur} == Sp.current(t, f) : Maybe<&2, String>}, hb: {False{} == String.eq(r, cur) : Bool}, hp: {None{} == Sp.chain(List.length(&2, Cl.Step, Sp.steps_of(t, f)), Sp.steps_of(t, f), cur, Sp.next(Sp.steps_of(t, f), r)) : Maybe<&2, List<&2, Cl.Step>>}) -> {Sp.lift_spec(t, Cl.Call{f, r, ks}) == Cl.Stranded{} : Cl.Lift}:
  %e : {Sp.lift_spec.cur(r, ks, _, Sp.steps_of(t, f)) == Cl.Stranded{} : Cl.Lift}
  %hb : {Sp.lift_spec.at(_, cur, ks, Sp.chain(List.length(&2, Cl.Step, Sp.steps_of(t, f)), Sp.steps_of(t, f), cur, Sp.next(Sp.steps_of(t, f), r))) == Cl.Stranded{} : Cl.Lift}
  %hp : {Sp.lift_spec.chain(cur, ks, _) == Cl.Stranded{} : Cl.Lift}
  {==}

# a current call, applied as stored, is current again
def clm.id.cur(+t: List<&2, Cl.Fam>, +f: String, +r: String, +ks: List<&2, String>, +cur: String, e: {Some{cur} == Sp.current(t, f) : Maybe<&2, String>}, hb: {True{} == String.eq(r, cur) : Bool}) -> {Sp.lift_spec(t, Cl.Call{f, r, ks}) == Cl.Current{} : Cl.Lift}:
  %e : {Sp.lift_spec.cur(r, ks, _, Sp.steps_of(t, f)) == Cl.Current{} : Cl.Lift}
  %hb : {Sp.lift_spec.at(_, cur, ks, Sp.chain(List.length(&2, Cl.Step, Sp.steps_of(t, f)), Sp.steps_of(t, f), cur, Sp.next(Sp.steps_of(t, f), r))) == Cl.Current{} : Cl.Lift}
  {==}

# an unknown call, applied as stored, is unknown again
def clm.id.unk(+t: List<&2, Cl.Fam>, +f: String, r: String, ks: List<&2, String>, e: {None{} == Sp.current(t, f) : Maybe<&2, String>}) -> {Sp.lift_spec(t, Cl.Call{f, r, ks}) == Cl.Unknown{} : Cl.Lift}:
  %e : {Sp.lift_spec.cur(r, ks, _, Sp.steps_of(t, f)) == Cl.Unknown{} : Cl.Lift}
  {==}

def clm.id.p(p: Maybe<&2, List<&2, Cl.Step>>, +t: List<&2, Cl.Fam>, +f: String, +r: String, +ks: List<&2, String>, +cur: String, e: {Some{cur} == Sp.current(t, f) : Maybe<&2, String>}, hb: {False{} == String.eq(r, cur) : Bool}) -> {p == Sp.chain(List.length(&2, Cl.Step, Sp.steps_of(t, f)), Sp.steps_of(t, f), cur, Sp.next(Sp.steps_of(t, f), r)) : Maybe<&2, List<&2, Cl.Step>>} -> {Sp.lift_spec(t, CallLift.applied.l(f, r, ks, Sp.lift_spec.chain(cur, ks, p))) == CallLift.settled(Sp.lift_spec.chain(cur, ks, p)) : Cl.Lift}:
  match p:
    case None{}:
      hp => clm.id.none(t, f, r, ks, cur, e, hb, hp)
    case Some{path}:
      hp => clm.id.st(Sp.ops(Sp.ops_of(path), Cl.St{Sp.stored(ks, 0n), []}), t, f, r, ks, cur, e)

def clm.id.b(b: Bool, +t: List<&2, Cl.Fam>, +f: String, +r: String, +ks: List<&2, String>, +cur: String, e: {Some{cur} == Sp.current(t, f) : Maybe<&2, String>}) -> {b == String.eq(r, cur) : Bool} -> {Sp.lift_spec(t, CallLift.applied.l(f, r, ks, Sp.lift_spec.at(b, cur, ks, Sp.chain(List.length(&2, Cl.Step, Sp.steps_of(t, f)), Sp.steps_of(t, f), cur, Sp.next(Sp.steps_of(t, f), r))))) == CallLift.settled(Sp.lift_spec.at(b, cur, ks, Sp.chain(List.length(&2, Cl.Step, Sp.steps_of(t, f)), Sp.steps_of(t, f), cur, Sp.next(Sp.steps_of(t, f), r)))) : Cl.Lift}:
  match b:
    case True{}:
      hb => clm.id.cur(t, f, r, ks, cur, e, hb)
    case False{}:
      hb => clm.id.p(Sp.chain(List.length(&2, Cl.Step, Sp.steps_of(t, f)), Sp.steps_of(t, f), cur, Sp.next(Sp.steps_of(t, f), r)), t, f, r, ks, cur, e, hb)({==})

def clm.id.m(m: Maybe<&2, String>, +t: List<&2, Cl.Fam>, +f: String, +r: String, +ks: List<&2, String>) -> {m == Sp.current(t, f) : Maybe<&2, String>} -> {Sp.lift_spec(t, CallLift.applied.l(f, r, ks, Sp.lift_spec.cur(r, ks, m, Sp.steps_of(t, f)))) == CallLift.settled(Sp.lift_spec.cur(r, ks, m, Sp.steps_of(t, f))) : Cl.Lift}:
  match m:
    case None{}:
      e => clm.id.unk(t, f, r, ks, e)
    case Some{+cur}:
      e => clm.id.b(String.eq(r, cur), t, f, r, ks, cur, e)({==})

def CallLift.call_lift_idempotent(t, c):
  match c:
    case Cl.Call{+f, +r, +ks}:
      %Equal.sym(Cl.Lift, Cl.lift(t, Cl.Call{f, r, ks}), Sp.lift_spec(t, Cl.Call{f, r, ks}), LCallLiftRefines.clm.refines(t, Cl.Call{f, r, ks})) : {Cl.lift(t, CallLift.applied(Cl.Call{f, r, ks}, _)) == CallLift.settled(_) : Cl.Lift}
      Equal.trans(Cl.Lift, Cl.lift(t, CallLift.applied(Cl.Call{f, r, ks}, Sp.lift_spec(t, Cl.Call{f, r, ks}))), Sp.lift_spec(t, CallLift.applied(Cl.Call{f, r, ks}, Sp.lift_spec(t, Cl.Call{f, r, ks}))), CallLift.settled(Sp.lift_spec(t, Cl.Call{f, r, ks})), LCallLiftRefines.clm.refines(t, CallLift.applied(Cl.Call{f, r, ks}, Sp.lift_spec(t, Cl.Call{f, r, ks}))), clm.id.m(Sp.current(t, f), t, f, r, ks)({==}))
