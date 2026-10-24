# eukhe: the proof of LAW log_stepper_reads_only_fitting_commits
#
# As log_stepper_reads_only_commits (pe.bools_exact), and the count fits
# the wire: an encoding whose count does not fit reads as no list
# (wire_nat_too_long), not as the list decoded.

import Base
import ../../bend/log.bend as Lr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/log.bend as Log
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nat_too_long.bend as PWireNatTooLong
import ./base.bend as LA

def pk.DT(d: Wr.Dec<List<&2, Bool>>, G: Type) -> Type:
  match d:
    case Wr.Got{x, r}:
      Unit
    case Wr.Bad{}:
      G

def pk.got_bad(-G: Type, -x: List<&2, Bool>, -r: String, e: {Wr.Got{x, r} == Wr.Bad{} : Wr.Dec<List<&2, Bool>>}) -> G:
  %e : pk.DT(_, G)
  Unit{}

# a decoded list's count fits
def pk.fits.at(b: Bool, +s: String, +ds: List<&2, Bool>, +rest: String, eb: {LawsBase.wire_fits(List.length(&2, Bool, ds)) == b : Bool}, ex: {s == Wr.put_list(~Bool, ~Wr.put_bool, ds, rest) : String}, h: {Wr.get_list(~Bool, ~Wr.get_bool, s) == Wr.Got{ds, rest} : Wr.Dec<List<&2, Bool>>}) -> {LawsBase.wire_fits(List.length(&2, Bool, ds)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +x = LA.pe.bools(ds, rest)
      +n = List.length(&2, Bool, ds)
      +c1 = Equal.trans(Wr.Dec<List<&2, Bool>>, Wr.Got{ds, rest}, Wr.get_list(~Bool, ~Wr.get_bool, s), Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_list(~Bool, ~Wr.put_bool, ds, rest)), Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, s), Wr.Got{ds, rest}, h), Equal.cong(String, Wr.Dec<List<&2, Bool>>, z => Wr.get_list(~Bool, ~Wr.get_bool, z), s, Wr.put_list(~Bool, ~Wr.put_bool, ds, rest), ex))
      +c2 = Equal.trans(Wr.Dec<List<&2, Bool>>, Wr.Got{ds, rest}, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_list(~Bool, ~Wr.put_bool, ds, rest)), Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)), c1, Equal.cong(String, Wr.Dec<List<&2, Bool>>, z => Wr.get_list(~Bool, ~Wr.get_bool, z), Wr.put_list(~Bool, ~Wr.put_bool, ds, rest), Wr.put_nat(n, x), LA.pe.put_list(ds, rest)))
      +c3 = Equal.trans(Wr.Dec<List<&2, Bool>>, Wr.Got{ds, rest}, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)), Wr.Bad{}, c2, Equal.cong(Wr.Dec<Nat>, Wr.Dec<List<&2, Bool>>, z => Wr.get_list.start(~Bool, ~Wr.get_bool, z), Wr.get_nat(Wr.put_nat(n, x)), Wr.Bad{}, Wire.wire_nat_too_long(n, x, eb)))
      pk.got_bad({LawsBase.wire_fits(List.length(&2, Bool, ds)) == True{} : Bool}, ds, rest, c3)

def pk.G(s: String) -> Type:
  &d: List<&2, Bool> -> ({s == Log.log_spell_sides(d) : String} & {LawsBase.wire_fits(List.length(&2, Bool, d)) == True{} : Bool})

def pk.end(rest: String, +s: String, -x: Lr.Store, +ds: List<&2, Bool>, ex: {s == Wr.put_list(~Bool, ~Wr.put_bool, ds, rest) : String}, fd: {LawsBase.wire_fits(List.length(&2, Bool, ds)) == True{} : Bool}, ok: {LawsBase.wire_opens_err(Log.log_reply(FLg.step.end(Wr.end(rest), x, ds))) == False{} : Bool}) -> pk.G(s):
  match rest:
    case SNil{}:
      (ds, (ex, fd))
    case SCon{c, t}:
      LLogicLogic.pt.absurd(pk.G(s), ok)

def pk.step(+s: String, -x: Lr.Store, r: Wr.Dec<List<&2, Bool>>, er: {Wr.get_list(~Bool, ~Wr.get_bool, s) == r : Wr.Dec<List<&2, Bool>>}, ok: {LawsBase.wire_opens_err(Log.log_reply(FLg.step.go(x, r))) == False{} : Bool}) -> pk.G(s):
  match r:
    case Wr.Got{+ds, +rest}:
      +er2 = er
      +ex = LA.pe.bools_exact(s, ds, rest, er2)
      pk.end(rest, s, x, ds, ex, pk.fits.at(LawsBase.wire_fits(List.length(&2, Bool, ds)), s, ds, rest, {==}, ex, er2), ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(pk.G(s), ok)

def Log.log_stepper_reads_only_fitting_commits(st, s, ok):
  match st:
    case FLg.Running{x}:
      pk.step(s, x, Wr.get_list(~Bool, ~Wr.get_bool, s), {==}, ok)
    case FLg.Shut{}:
      LLogicLogic.pt.absurd(pk.G(s), ok)
