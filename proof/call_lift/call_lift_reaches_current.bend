# eukhe: the proof of LAW call_lift_reaches_current
#
# PROOF: the lookup finds the family (cll.fam_found); the call is not at its current rev (the premise), and the walk from the step leaving r follows the chain ys (cll.walk_chain, induction on ys and the fuel: each step found arrives at the chain's next rev, String.eq soundness turning the test into that rev; the current rev ends it, else the walk goes on), answering the chain's ops; the lift applies them to the stored arguments (kept == stored, cll.kept_stored) and stamps the current rev (cll.done_as).

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift
import ./base/lookup.bend as LCallLiftLookup

def CallLift.call_lift_reaches_current(pre, post, f, cur, ss, r, ks, ys, first, old, chain, short):
  %Equal.sym(Maybe<&2, Cl.Fam>, Cl.fam_of(List.append(&2, Cl.Fam, pre, Cl.Fam{f, cur, ss} <> post), f), Some{Cl.Fam{f, cur, ss}}, LCallLiftLookup.cll.fam_found(pre, post, f, cur, ss, first)) : {Cl.lift.fam(r, ks, _) == CallLift.lifted_as(cur, Cl.apply_ops(CallLift.chain_ops(ys, ss, r), Cl.St{CallLift.stored(ks, 0n), []})) : Cl.Lift}
  %Equal.sym(Bool, String.eq(r, cur), False{}, old) : {Cl.lift.at(_, cur, ks, Cl.walk(List.length(&2, Cl.Step, ss), ss, cur, Cl.step_of(ss, r))) == CallLift.lifted_as(cur, Cl.apply_ops(CallLift.chain_ops(ys, ss, r), Cl.St{CallLift.stored(ks, 0n), []})) : Cl.Lift}
  %Equal.sym(Maybe<&2, List<&2, Cl.Op>>, Cl.walk(List.length(&2, Cl.Step, ss), ss, cur, Cl.step_of(ss, r)), Some{CallLift.chain_ops(ys, ss, r)}, LCallLiftLookup.cll.walk_chain(ys, List.length(&2, Cl.Step, ss), ss, cur, r, chain, short)) : {Cl.lift.path(cur, ks, _) == CallLift.lifted_as(cur, Cl.apply_ops(CallLift.chain_ops(ys, ss, r), Cl.St{CallLift.stored(ks, 0n), []})) : Cl.Lift}
  %LCallLiftLookup.cll.kept_stored(ks, 0n) : {Cl.lift.done(cur, Cl.apply_ops(CallLift.chain_ops(ys, ss, r), Cl.St{_, []})) == CallLift.lifted_as(cur, Cl.apply_ops(CallLift.chain_ops(ys, ss, r), Cl.St{CallLift.stored(ks, 0n), []})) : Cl.Lift}
  LCallLiftLookup.cll.done_as(cur, Cl.apply_ops(CallLift.chain_ops(ys, ss, r), Cl.St{CallLift.stored(ks, 0n), []}))
