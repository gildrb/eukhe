# eukhe: the proof of LAW dash_rejected_runs_nothing

import Base
import ../../bend/dash.bend as Da
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pa.rejected_no(c: Nat, b: Bool, +h: {Da.is_paired(Da.open.out(c, b)) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LA.dashboard_auth.pa.absurdT({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# a rejected open leaves its connection stale
def pa.rejected_stale(+s: Da.St, +c: Nat, +shown: Maybe<&2, Nat>, +rejected: {Da.is_paired(Da.out(s, Da.Open{c, shown})) == False{} : Bool}) -> {LA.pa.stale(Da.St.cur(Da.next(s, Da.Open{c, shown})), Da.held(c, Da.St.conns(Da.next(s, Da.Open{c, shown})))) == True{} : Bool}:
  match s:
    case Da.St{+cur, +cs}:
      match shown:
        case None{}:
          %Equal.sym(Maybe<&2, Nat>, Da.held(c, Da.drop(c, cs)), None{}, LA.pa.held_drop_same(c, cs)) : {LA.pa.stale(cur, _) == True{} : Bool}
          {==}
        case Some{+t}:
          %Equal.sym(Bool, Nat.is_eq(t, cur), False{}, pa.rejected_no(c, Nat.is_eq(t, cur), rejected)) : {LA.pa.stale(cur, Da.held(c, Da.open.keep(c, t, _, Da.drop(c, cs)))) == True{} : Bool}
          %Equal.sym(Maybe<&2, Nat>, Da.held(c, Da.drop(c, cs)), None{}, LA.pa.held_drop_same(c, cs)) : {LA.pa.stale(cur, _) == True{} : Bool}
          {==}

def pa.rejected_runs_nothing(+s: Da.St, +c: Nat, +shown: Maybe<&2, Nat>, +evs: List<&2, Da.Ev>, +rejected: {Da.is_paired(Da.out(s, Da.Open{c, shown})) == False{} : Bool}, +again: {Da.any_opens(c, evs) == False{} : Bool}) -> {Da.any_ran(c, Da.run(Da.Open{c, shown} <> evs, s)) == False{} : Bool}:
  %Equal.sym(Bool, Da.ran(c, Da.out(s, Da.Open{c, shown})), False{}, LA.pa.open_not_ran(c, c, Da.admit(Da.St.cur(s), shown))) : {Bool.or(_, Da.any_ran(c, Da.run(evs, Da.next(s, Da.Open{c, shown})))) == False{} : Bool}
  LA.pa.quiet(evs, Da.next(s, Da.Open{c, shown}), c, pa.rejected_stale(s, c, shown, rejected), again)

def Laws.dash_rejected_runs_nothing(s, c, shown, evs, rejected, again):
  pa.rejected_runs_nothing(s, c, shown, evs, rejected, again)
