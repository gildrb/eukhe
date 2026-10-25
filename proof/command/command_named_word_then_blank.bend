# eukhe: the proof of LAW command_named_word_then_blank
#
# PROOF of LAW command_named_word_then_blank: the walk lands after the
# named word on its entry (nm_walk_line), the blank rest leaves it there
# (nm_blank_walk), and the entry finishes as itself (nm_finish_ent).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base.bend as LA
import ./base/named.bend as LACommandNamed
import ../base/logic/bool.bend as LLogicBool

def CommandNamed.command_named_word_then_blank(t, q, w, e, gs, s, ok, on, word, hit, blank):
  +W = {Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> s)), t, Cmd.Top{}), Cmd.walk(Cmd.words(s), t, W), LACommandNamed.nm_walk_line(t, q, w, e, gs, 32n <> s, ok, on, word, hit, {==})) : {Cmd.finish(_, t) == CommandNamed.cmd_ent_ended(t, e) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(s), t, W), W, LACommandNamed.nm_blank_walk(t, Cmd.Ent.path(e), e, s, blank)) : {Cmd.finish(_, t) == CommandNamed.cmd_ent_ended(t, e) : Cmd.Res}
  LACommandNamed.nm_finish_ent(t, e)
