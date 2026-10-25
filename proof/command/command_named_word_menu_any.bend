# eukhe: the proof of LAW command_named_word_menu_any
#
# PROOF of LAW command_named_word_menu_any: the named entry's path is
# declared (nm_named_decl), so it has a first entry e1, which its
# canonical last name names (nm_canon_hit); both lines walk onto that path
# (with e and with e1) before the text (nm_menu_line), and a menu never
# reads the entry of the path it walks from (nm_menu_after_any).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base.bend as LA
import ./base/named.bend as LACommandNamed
import ../base/logic/bool.bend as LLogicBool

def CommandNamed.command_named_word_menu_any(t, q, w, e, gs, s, ok, on, word, hit):
  +ok2 = ok
  +on2 = on
  +hit2 = hit
  +pe = Command.cmd_ent_path(e)
  +y = Command.cmd_last(pe)
  +qy = List.append(&2, List<&2, Nat>, q, [y])
  +dP = LACommandNamed.nm_named_decl(t, q, w, e, hit2)
  +e1 = LACommandNamed.nm_first.of(Command.cmd_lookup(t, pe), dP)
  +first = LACommandNamed.nm_first.eq(Command.cmd_lookup(t, pe), dP)
  +ty = LLogicBool.cb_and_l(Command.cmd_typed(y), Command.cmd_eq(Command.cmd_lower(y), y), LACommandNamed.nm_canon_name(t, q, w, e, e1, ok2, hit2, first))
  +hy = LACommandNamed.nm_canon_hit(t, q, w, e, e1, ok2, hit2, first)
  %Equal.sym(List<&2, List<&2, Nat>>, pe, qy, LACommandNamed.nm_path(t, q, w, e, hit2)) : {Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> s)) == Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(_, gs), 32n <> s)) : Cmd.Menu}
  %Equal.sym(Cmd.Menu, Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> s)), LACommandNamed.nm_menu_after(Cmd.cut(Cmd.words(s)), t, Cmd.Walk{Cmd.Ent.path(e), e}), LACommandNamed.nm_menu_line(t, q, w, e, gs, s, ok2, on2, word, hit2)) : {_ == Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(qy, gs), 32n <> s)) : Cmd.Menu}
  %Equal.sym(Cmd.Menu, Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(qy, gs), 32n <> s)), LACommandNamed.nm_menu_after(Cmd.cut(Cmd.words(s)), t, Cmd.Walk{Cmd.Ent.path(e1), e1}), LACommandNamed.nm_menu_line(t, q, y, e1, gs, s, ok2, on2, ty, hy)) : {LACommandNamed.nm_menu_after(Cmd.cut(Cmd.words(s)), t, Cmd.Walk{Cmd.Ent.path(e), e}) == _ : Cmd.Menu}
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.Ent.path(e1), Cmd.Ent.path(e), LACommandNamed.nm_first_path(t, e, e1, first)) : {LACommandNamed.nm_menu_after(Cmd.cut(Cmd.words(s)), t, Cmd.Walk{Cmd.Ent.path(e), e}) == LACommandNamed.nm_menu_after(Cmd.cut(Cmd.words(s)), t, Cmd.Walk{_, e1}) : Cmd.Menu}
  LACommandNamed.nm_menu_after_any(Cmd.cut(Cmd.words(s)), t, Cmd.Ent.path(e), e, e1)
