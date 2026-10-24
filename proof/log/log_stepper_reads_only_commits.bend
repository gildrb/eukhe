# eukhe: the proof of LAW log_stepper_reads_only_commits
#
# A list of Bools that reads gives the prefix of the input
# (pe.bools_exact); input left over, no list or a refused open answers the
# error form, which the premise refutes.

import Base
import ../../bend/log.bend as Lr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def pl.end(rest: String, +s: String, -x: Lr.Store, +ds: List<&2, Bool>, ex: {s == Wr.put_list(~Bool, ~Wr.put_bool, ds, rest) : String}, ok: {LawsBase.wire_opens_err(Log.log_reply(FLg.step.end(Wr.end(rest), x, ds))) == False{} : Bool}) -> &d: List<&2, Bool> -> {s == Log.log_spell_sides(d) : String}:
  match rest:
    case SNil{}:
      (ds, ex)
    case SCon{c, t}:
      LLogicLogic.pt.absurd(&d: List<&2, Bool> -> {s == Log.log_spell_sides(d) : String}, ok)

def pl.step(+s: String, -x: Lr.Store, r: Wr.Dec<List<&2, Bool>>, er: {Wr.get_list(~Bool, ~Wr.get_bool, s) == r : Wr.Dec<List<&2, Bool>>}, ok: {LawsBase.wire_opens_err(Log.log_reply(FLg.step.go(x, r))) == False{} : Bool}) -> &d: List<&2, Bool> -> {s == Log.log_spell_sides(d) : String}:
  match r:
    case Wr.Got{+ds, +rest}:
      pl.end(rest, s, x, ds, LA.pe.bools_exact(s, ds, rest, er), ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(&d: List<&2, Bool> -> {s == Log.log_spell_sides(d) : String}, ok)

def Log.log_stepper_reads_only_commits(st, s, ok):
  match st:
    case FLg.Running{x}:
      pl.step(s, x, Wr.get_list(~Bool, ~Wr.get_bool, s), {==}, ok)
    case FLg.Shut{}:
      LLogicLogic.pt.absurd(&d: List<&2, Bool> -> {s == Log.log_spell_sides(d) : String}, ok)
