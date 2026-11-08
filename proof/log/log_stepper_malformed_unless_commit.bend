# eukhe: the proof of LAW log_stepper_malformed_unless_commit
#
# A decoded list of Bools is exactly its encoding (pe.bools_exact) and its
# count fits (pk.fits.at of log_stepper_reads_only_fitting_commits); no
# list answers the malformed commit, which the premise refutes.

import Base
import ../../bend/log.bend as Lr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA
import ./log_stepper_reads_only_fitting_commits.bend as PLogStepperReadsOnlyFittingCommits

def lmc.pair(+s: String, +x: String, +b: Bool, e1: {s == x : String}, e2: {b == True{} : Bool}) -> {(s, b) == (x, True{}) : String & Bool}:
  %Equal.sym(String, s, x, e1) : {(_, b) == (x, True{}) : String & Bool}
  %Equal.sym(Bool, b, True{}, e2) : {(x, _) == (x, True{}) : String & Bool}
  {==}

def lmc.G(+s: String) -> Type:
  &ds: List<&2, Bool> -> &rest: String -> {(s, LawsBase.wire_fits(List.length(&2, Bool, ds))) == (Wr.put_list(~Bool, ~Wr.put_bool, ds, rest), True{}) : String & Bool}

def lmc.step(+s: String, -x: Lr.Store, r: Wr.Dec<List<&2, Bool>>, er: {Wr.get_list(~Bool, ~Wr.get_bool, s) == r : Wr.Dec<List<&2, Bool>>}, other: {String.eq(Log.log_reply(FLg.step.go(x, r)), Wr.err("log: malformed commit")) == False{} : Bool}) -> lmc.G(s):
  match r:
    case Wr.Got{+ds, +rest}:
      +er2 = er
      +ex = LA.pe.bools_exact(s, ds, rest, er2)
      +fd = PLogStepperReadsOnlyFittingCommits.pk.fits.at(LawsBase.wire_fits(List.length(&2, Bool, ds)), s, ds, rest, {==}, ex, er2)
      (ds, (rest, lmc.pair(s, Wr.put_list(~Bool, ~Wr.put_bool, ds, rest), LawsBase.wire_fits(List.length(&2, Bool, ds)), ex, fd)))
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(lmc.G(s), other)

def Log.log_stepper_malformed_unless_commit(st, s, other):
  lmc.step(s, st, Wr.get_list(~Bool, ~Wr.get_bool, s), {==}, other)
