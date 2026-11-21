# eukhe: the proof of LAW command_ffi_menu_exact
#
# PROOF of LAW command_ffi_menu_exact: the menu reply reader reads a tag,
# then for the children a path and a list of places; each stage is a wire
# value its exactness law inverts (wire_nat_exact, wire_strs_exact,
# wire_list_exact, spelled by wire_nats_spells), threading the equation of
# the input so far, and a decoded list fits (wire_strs_decoded_fit,
# LACommandReply.cr_nats_fit), so an accepted reply is the grammar's
# spelling of what it read, then the rest, and fits.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ../wire/base/spell.bend as LAWireSpell
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_strs_exact.bend as PWireStrsExact
import ../wire/wire_list_exact.bend as PWireListExact
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ./base/reply.bend as LACommandReply

# what a menu reply reader answer says about its input s
def cmx_menu(s: String, d: Wr.Dec<FCmd.MenuW>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == Command.cmd_spell_menuw(x, r) : String} & {Command.cmd_menu_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a list of places the reader accepts is its spelling
def cmx_nats(+s2: String, +xs: List<&2, Nat>, +s3: String, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s2) == Wr.Got{xs, s3} : Wr.Dec<List<&2, Nat>>}) -> {s2 == LawsBase.wire_spell_nats(xs, s3) : String}:
  Equal.trans(String, s2, Wr.put_list(~Nat, ~Wr.put_nat, xs, s3), LawsBase.wire_spell_nats(xs, s3), Wire.wire_list_exact(s2, xs, s3, ed), Wire.wire_nats_spells(xs, s3))

def cmx_items(-s0: String, +p: List<&2, String>, +s2: String, pre: {s0 == Wr.put_nat(1n, LawsBase.wire_spell_strs(p, s2)) : String},
  fp: {Command.cmd_strs_fit(p) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s2) == d : Wr.Dec<List<&2, Nat>>}) -> cmx_menu(s0, FCmd.get_menu.items(p, d)):
  match d:
    case Wr.Got{+xs, +s3}:
      +e2 = ed
      (Equal.trans(String, s0, Wr.put_nat(1n, LawsBase.wire_spell_strs(p, s2)), Wr.put_nat(1n, LawsBase.wire_spell_strs(p, LawsBase.wire_spell_nats(xs, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, LawsBase.wire_spell_strs(p, z)), s2, LawsBase.wire_spell_nats(xs, s3), cmx_nats(s2, xs, s3, e2))),
        LAWireSpell.ws_and_tt(Command.cmd_strs_fit(p), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), fp, LACommandReply.cr_nats_fit(s2, xs, s3, e2)))
    case Wr.Bad{}:
      Unit{}

def cmx_kids(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(1n, s1) : String},
  d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s1) == d : Wr.Dec<List<&2, String>>}) -> cmx_menu(s0, FCmd.get_menu.kids(d)):
  match d:
    case Wr.Got{+p, +s2}:
      +e2 = ed
      cmx_items(s0, p, s2,
        Equal.trans(String, s0, Wr.put_nat(1n, s1), Wr.put_nat(1n, LawsBase.wire_spell_strs(p, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, LawsBase.wire_spell_strs(p, s2), Wire.wire_strs_exact(s1, p, s2, e2))),
        LACommandReply.cr_strs_fit(s1, p, s2, e2),
        Wr.get_list(~Nat, ~Wr.get_nat, s2), {==})
    case Wr.Bad{}:
      Unit{}

def cmx_tag(+s0: String, t: Nat, +s1: String, ex: {s0 == Wr.put_nat(t, s1) : String}) -> cmx_menu(s0, FCmd.get_menu.tag(t, s1)):
  match t:
    case 0n:
      (ex, {==})
    case 1n:
      cmx_kids(s0, s1, ex, FCmd.get_strs(s1), {==})
    case 2n:
      (ex, {==})
    case 3n+y:
      Unit{}

def cmx_go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cmx_menu(s, FCmd.get_menu.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      cmx_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

# every menu reply the reader accepts is its spelling, and fits
def cmx_all(+s: String) -> cmx_menu(s, FCmd.get_menu(s)):
  cmx_go(s, Wr.get_nat(s), {==})

def cmx_at(+s: String, -d: Wr.Dec<FCmd.MenuW>, er: {FCmd.get_menu(s) == d : Wr.Dec<FCmd.MenuW>}) -> cmx_menu(s, d):
  %er : cmx_menu(s, _)
  cmx_all(s)

def Command.command_ffi_menu_exact(s, x, rest, h):
  LACommandReply.cr_pair(s, Command.cmd_spell_menuw(x, rest), Command.cmd_menu_fits(x), cmx_at(s, Wr.Got{x, rest}, h))
