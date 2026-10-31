# eukhe: the proof of LAW call_lift_reaches_current
#
# PROOF: the lift is the spec's (call_lift_refines_spec); a known rev has a family (else known is False), and there either it is the current rev (current, at the current rev) or its chain arrives (else known is False), so the spec lifts the call to the current rev, which is the family's current rev by String.eq reflexivity (clm.str_refl).

import Base
import ../../bend/call_lift.bend as Cl
import ../../spec/harness/lift.bend as Sp
import ../../laws/call_lift.bend as CallLift
import ./base/string.bend as LCallLiftString
import ./call_lift_refines_spec.bend as PCallLiftRefinesSpec

def clm.rc.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

def clm.rc.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %Equal.sym(Bool, False{}, True{}, e) : clm.rc.If(_, G)
  Unit{}

def clm.rc.done(+cur: String, st: Cl.St, +t: List<&2, Cl.Fam>, +f: String, e: {Some{cur} == Sp.current(t, f) : Maybe<&2, String>}) -> {Sp.at_current(t, f, Sp.lift_spec.done(cur, st)) == True{} : Bool}:
  match st:
    case Cl.St{a, rs}:
      %e : {Sp.same_rev(cur, _) == True{} : Bool}
      LCallLiftString.clm.str_refl(cur)

def clm.rc.p(p: Maybe<&2, List<&2, Cl.Step>>, +cur: String, +ks: List<&2, String>, +t: List<&2, Cl.Fam>, +f: String, e: {Some{cur} == Sp.current(t, f) : Maybe<&2, String>}) -> {Sp.arrives(p) == True{} : Bool} -> {Sp.at_current(t, f, Sp.lift_spec.chain(cur, ks, p)) == True{} : Bool}:
  match p:
    case None{}:
      k => clm.rc.absurd({Sp.at_current(t, f, Cl.Stranded{}) == True{} : Bool}, k)
    case Some{path}:
      k => clm.rc.done(cur, Sp.ops(Sp.ops_of(path), Cl.St{Sp.stored(ks, 0n), []}), t, f, e)

def clm.rc.at(at: Bool, +cur: String, +ks: List<&2, String>, p: Maybe<&2, List<&2, Cl.Step>>, +t: List<&2, Cl.Fam>, +f: String, e: {Some{cur} == Sp.current(t, f) : Maybe<&2, String>}) -> {Bool.or(at, Sp.arrives(p)) == True{} : Bool} -> {Sp.at_current(t, f, Sp.lift_spec.at(at, cur, ks, p)) == True{} : Bool}:
  match at:
    case True{}:
      k => {==}
    case False{}:
      k => clm.rc.p(p, cur, ks, t, f, e)(k)

def clm.rc.m(m: Maybe<&2, String>, +r: String, +ks: List<&2, String>, +t: List<&2, Cl.Fam>, +f: String) -> {m == Sp.current(t, f) : Maybe<&2, String>} -> {Sp.known.at(r, m, Sp.steps_of(t, f)) == True{} : Bool} -> {Sp.at_current(t, f, Sp.lift_spec.cur(r, ks, m, Sp.steps_of(t, f))) == True{} : Bool}:
  match m:
    case None{}:
      e => k => clm.rc.absurd({Sp.at_current(t, f, Cl.Unknown{}) == True{} : Bool}, k)
    case Some{+cur}:
      e => k => clm.rc.at(String.eq(r, cur), cur, ks, Sp.chain(List.length(&2, Cl.Step, Sp.steps_of(t, f)), Sp.steps_of(t, f), cur, Sp.next(Sp.steps_of(t, f), r)), t, f, e)(k)

def CallLift.call_lift_reaches_current(t, f, r, ks, known):
  %Equal.sym(Cl.Lift, Cl.lift(t, Cl.Call{f, r, ks}), Sp.lift_spec(t, Cl.Call{f, r, ks}), CallLift.call_lift_refines_spec(t, Cl.Call{f, r, ks})) : {Sp.at_current(t, f, _) == True{} : Bool}
  clm.rc.m(Sp.current(t, f), r, ks, t, f)({==})(known)
