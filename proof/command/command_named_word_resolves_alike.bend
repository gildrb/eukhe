# eukhe: the proof of LAW command_named_word_resolves_alike
#
# PROOF of LAW command_named_word_resolves_alike: as
# command_named_word_resolves, the canonical name walking onto the path
# with its first entry e1 (nm_canon_hit); e and e1 have one path
# (nm_first_path) and run and take text alike (nm_alike_run,
# nm_alike_free), so the text after the word finishes alike
# (nm_finish_alike).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base.bend as LA
import ./base/named.bend as LACommandNamed
import ../base/logic/bool.bend as LLogicBool

def CommandNamed.command_named_word_resolves_alike(t, q, w, e, e1, gs, s, ok, on, word, hit, first, alike, gap):
  +ok2 = ok
  +on2 = on
  +hit2 = hit
  +first2 = first
  +alike2 = alike
  +gap2 = gap
  +pe = Command.cmd_ent_path(e)
  +y = Command.cmd_last(pe)
  +qy = List.append(&2, List<&2, Nat>, q, [y])
  +ty = LLogicBool.cb_and_l(Command.cmd_typed(y), Command.cmd_eq(Command.cmd_lower(y), y), LACommandNamed.nm_canon_name(t, q, w, e, e1, ok2, hit2, first2))
  +hy = LACommandNamed.nm_canon_hit(t, q, w, e, e1, ok2, hit2, first2)
  +Y = LACommandNamed.nm_tail(s)
  %Equal.sym(List<&2, List<&2, Nat>>, pe, qy, LACommandNamed.nm_path(t, q, w, e, hit2)) : {Cmd.resolve(t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), s)) == Cmd.resolve(t, List.append(&2, Nat, Command.cmd_loose(_, gs), s)) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), s)), t, Cmd.Top{}), Cmd.walk(Y, t, Cmd.Walk{Cmd.Ent.path(e), e}), LACommandNamed.nm_walk_line(t, q, w, e, gs, s, ok2, on2, word, hit2, gap2)) : {Cmd.finish(_, t) == Cmd.resolve(t, List.append(&2, Nat, Command.cmd_loose(qy, gs), s)) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(List.append(&2, Nat, Command.cmd_loose(qy, gs), s)), t, Cmd.Top{}), Cmd.walk(Y, t, Cmd.Walk{Cmd.Ent.path(e1), e1}), LACommandNamed.nm_walk_line(t, q, y, e1, gs, s, ok2, on2, ty, hy, gap2)) : {Cmd.finish(Cmd.walk(Y, t, Cmd.Walk{Cmd.Ent.path(e), e}), t) == Cmd.finish(_, t) : Cmd.Res}
  +hp = LACommandNamed.nm_first_path(t, e, e1, first2)
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.Ent.path(e1), Cmd.Ent.path(e), hp) : {Cmd.finish(Cmd.walk(Y, t, Cmd.Walk{Cmd.Ent.path(e), e}), t) == Cmd.finish(Cmd.walk(Y, t, Cmd.Walk{_, e1}), t) : Cmd.Res}
  LACommandNamed.nm_finish_alike(Y, t, Cmd.Ent.path(e), e, e1, LACommandNamed.nm_alike_run(e1, e, alike2), LACommandNamed.nm_alike_free(e1, e, alike2), hp)
