# eukhe: the proof of LAW command_named_word_ends
#
# PROOF of LAW command_named_word_ends: the walk over the line's words
# lands after the named word on the entry's path with that entry
# (nm_walk_line, nothing after it), which finishes as the entry's own
# answer (nm_finish_ent).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base.bend as LA
import ./base/named.bend as LACommandNamed
import ../base/logic/bool.bend as LLogicBool

def CommandNamed.command_named_word_ends(t, q, w, e, gs, ok, on, word, hit):
  +L = Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs)
  %LA.cb_app_nil(Nat, L) : {Cmd.finish(Cmd.walk(Cmd.words(_), t, Cmd.Top{}), t) == CommandNamed.cmd_ent_ended(t, e) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(List.append(&2, Nat, L, Nil{})), t, Cmd.Top{}), Cmd.walk(Nil{}, t, Cmd.Walk{Cmd.Ent.path(e), e}), LACommandNamed.nm_walk_line(t, q, w, e, gs, Nil{}, ok, on, word, hit, {==})) : {Cmd.finish(_, t) == CommandNamed.cmd_ent_ended(t, e) : Cmd.Res}
  LACommandNamed.nm_finish_ent(t, e)
