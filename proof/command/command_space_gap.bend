# eukhe: the proof of LAW command_space_gap
#
# PROOF of LAW command_space_gap: the names of a declared path q are
# spaceless (cmd_wf), so the words of its line, a space and text are q
# and the words of the text after the space (LSp.sp_words_render); a
# second space adds one empty word between them. The walk over q lands
# on q (the path with its entry), where the empty word changes nothing
# (LSp.sp_walk_gap: step.empty keeps a walk at a path), so the rest of
# the walk, and what the line resolves to, is the same.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA
import ./base/space.bend as LSp

def Command.command_space_gap(t, q, line, ok, on):
  match q:
    case Nil{}:
      LLogicLogic.cb_absurd({Cmd.resolve(t, List.append(&2, Nat, Command.cmd_render(Nil{}), 32n <> 32n <> line)) == Cmd.resolve(t, List.append(&2, Nat, Command.cmd_render(Nil{}), 32n <> line)) : Cmd.Res}, on)
    case Con{+x, +rest}:
      +k = ok
      +o = on
      +hs = LA.cb_names_spaceless(x <> rest, LA.cb_walks_names(t, x <> rest, k, o))
      +w = Cmd.words(line)
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(List.append(&2, Nat, Command.cmd_render(x <> rest), 32n <> 32n <> line)), x <> List.append(&2, List<&2, Nat>, rest, Nil{} <> w), LSp.sp_words_render(x, rest, 32n <> 32n <> line, Nil{} <> w, hs, {==})) : {Cmd.finish(Cmd.walk(_, t, Cmd.Top{}), t) == Cmd.resolve(t, List.append(&2, Nat, Command.cmd_render(x <> rest), 32n <> line)) : Cmd.Res}
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(List.append(&2, Nat, Command.cmd_render(x <> rest), 32n <> line)), x <> List.append(&2, List<&2, Nat>, rest, w), LSp.sp_words_render(x, rest, 32n <> line, w, hs, {==})) : {Cmd.finish(Cmd.walk(x <> List.append(&2, List<&2, Nat>, rest, Nil{} <> w), t, Cmd.Top{}), t) == Cmd.finish(Cmd.walk(_, t, Cmd.Top{}), t) : Cmd.Res}
      %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, x <> rest, Nil{} <> w), t, Cmd.Top{}), Cmd.walk(List.append(&2, List<&2, Nat>, x <> rest, w), t, Cmd.Top{}), LSp.sp_walk_gap(t, x <> rest, w, k, o)) : {Cmd.finish(_, t) == Cmd.finish(Cmd.walk(x <> List.append(&2, List<&2, Nat>, rest, w), t, Cmd.Top{}), t) : Cmd.Res}
      {==}
