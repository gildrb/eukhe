# eukhe: the proof of LAW command_named_word_then_other
#
# PROOF of LAW command_named_word_then_other: the walk lands after the
# named word on its entry before x (nm_walk_then); x names no child, so
# the entry's own flag starts argument text or an unknown word
# (nm_step_other), which takes the rest (nm_finish_miss: the text joins
# back as typed, nm_join_tail).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base.bend as LA
import ./base/named.bend as LACommandNamed
import ../base/logic/bool.bend as LLogicBool

def CommandNamed.command_named_word_then_other(t, q, w, e, gs, n, x, s, ok, on, word, hit, next, miss, gap):
  +next2 = next
  +gap2 = gap
  +pe = Command.cmd_ent_path(e)
  +Y = LACommandNamed.nm_tail(s)
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> List.append(&2, Nat, Command.cmd_spaces(n), List.append(&2, Nat, x, s)))), t, Cmd.Top{}), Cmd.walk(Y, t, Cmd.step(Cmd.Walk{Cmd.Ent.path(e), e}, t, x)), LACommandNamed.nm_walk_then(t, q, w, e, gs, n, x, s, ok, on, word, hit, LA.cb_typed_spaceless(x, next2), gap2)) : {Cmd.finish(_, t) == CommandNamed.cmd_named_miss(e, x, s) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.step(Cmd.Walk{Cmd.Ent.path(e), e}, t, x), Cmd.step.miss(Cmd.Ent.free(e), pe, x), LACommandNamed.nm_step_other(t, e, x, next2, miss)) : {Cmd.finish(Cmd.walk(Y, t, _), t) == CommandNamed.cmd_named_miss(e, x, s) : Cmd.Res}
  %Equal.sym(Cmd.Res, CommandNamed.cmd_named_miss(e, x, s), CommandNamed.cmd_named_miss.at(Cmd.Ent.free(e), pe, x, s), LACommandNamed.nm_named_miss(e, x, s)) : {Cmd.finish(Cmd.walk(Y, t, Cmd.step.miss(Cmd.Ent.free(e), pe, x)), t) == _ : Cmd.Res}
  LACommandNamed.nm_finish_miss(Cmd.Ent.free(e), t, pe, x, s, gap2)
