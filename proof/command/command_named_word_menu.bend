# eukhe: the proof of LAW command_named_word_menu
#
# PROOF of LAW command_named_word_menu: as command_named_word_resolves,
# with the menu: the loose words of q and w, then a space and any text,
# cut before the text's last word and walk onto e's path with e before
# the text (nm_menu_line), for w and for the canonical name y alike.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base/named.bend as LACommandNamed
import ../base/logic/bool.bend as LLogicBool

def CommandNamed.command_named_word_menu(t, q, w, e, gs, s, ok, on, word, hit, first):
  +ok2 = ok
  +on2 = on
  +hit2 = hit
  +first2 = first
  +pe = Command.cmd_ent_path(e)
  +y = Command.cmd_last(pe)
  +qy = List.append(&2, List<&2, Nat>, q, [y])
  +ty = LLogicBool.cb_and_l(Command.cmd_typed(y), Command.cmd_eq(Command.cmd_lower(y), y), LACommandNamed.nm_canon_name(t, q, w, e, ok2, hit2, first2))
  +hy = LACommandNamed.nm_canon_hit(t, q, w, e, ok2, hit2, first2)
  -M = LACommandNamed.nm_menu_after(Cmd.cut(Cmd.words(s)), t, Cmd.Walk{Cmd.Ent.path(e), e})
  %Equal.sym(List<&2, List<&2, Nat>>, pe, qy, LACommandNamed.nm_path(t, q, w, e, hit2)) : {Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> s)) == Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(_, gs), 32n <> s)) : Cmd.Menu}
  %Equal.sym(Cmd.Menu, Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> s)), M, LACommandNamed.nm_menu_line(t, q, w, e, gs, s, ok2, on2, word, hit2)) : {_ == Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(qy, gs), 32n <> s)) : Cmd.Menu}
  %Equal.sym(Cmd.Menu, Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(qy, gs), 32n <> s)), M, LACommandNamed.nm_menu_line(t, q, y, e, gs, s, ok2, on2, ty, hy)) : {M == _ : Cmd.Menu}
  {==}
