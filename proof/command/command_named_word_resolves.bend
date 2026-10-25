# eukhe: the proof of LAW command_named_word_resolves
#
# PROOF of LAW command_named_word_resolves: the named entry's path is q
# and its last name y (nm_path), a name that names the same entry
# (nm_canon_hit). The loose words of q and w, and of q and y, walk to
# the state of q, then both words step onto e's path with e (nm_walk_line);
# the text after them walks from there the same way, so both lines
# finish alike.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base/named.bend as LACommandNamed
import ../base/logic/bool.bend as LLogicBool

def CommandNamed.command_named_word_resolves(t, q, w, e, gs, s, ok, on, word, hit, first, gap):
  +ok2 = ok
  +on2 = on
  +hit2 = hit
  +first2 = first
  +gap2 = gap
  +pe = Command.cmd_ent_path(e)
  +y = Command.cmd_last(pe)
  +qy = List.append(&2, List<&2, Nat>, q, [y])
  +ty = LLogicBool.cb_and_l(Command.cmd_typed(y), Command.cmd_eq(Command.cmd_lower(y), y), LACommandNamed.nm_canon_name(t, q, w, e, e, ok2, hit2, first2))
  +hy = LACommandNamed.nm_canon_hit(t, q, w, e, e, ok2, hit2, first2)
  -W = {Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
  %Equal.sym(List<&2, List<&2, Nat>>, pe, qy, LACommandNamed.nm_path(t, q, w, e, hit2)) : {Cmd.resolve(t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), s)) == Cmd.resolve(t, List.append(&2, Nat, Command.cmd_loose(_, gs), s)) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), s)), t, Cmd.Top{}), Cmd.walk(LACommandNamed.nm_tail(s), t, W), LACommandNamed.nm_walk_line(t, q, w, e, gs, s, ok2, on2, word, hit2, gap2)) : {Cmd.finish(_, t) == Cmd.resolve(t, List.append(&2, Nat, Command.cmd_loose(qy, gs), s)) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(List.append(&2, Nat, Command.cmd_loose(qy, gs), s)), t, Cmd.Top{}), Cmd.walk(LACommandNamed.nm_tail(s), t, W), LACommandNamed.nm_walk_line(t, q, y, e, gs, s, ok2, on2, ty, hy, gap2)) : {Cmd.finish(Cmd.walk(LACommandNamed.nm_tail(s), t, W), t) == Cmd.finish(_, t) : Cmd.Res}
  {==}
