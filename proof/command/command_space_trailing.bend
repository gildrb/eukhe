# eukhe: the proof of LAW command_space_trailing
#
# PROOF of LAW command_space_trailing: the names of a declared path q are
# spaceless (cmd_wf), so the words of its line and a space are q and one
# empty word (LSp.sp_words_render), and the words of its line are q
# (LA.cb_words_render). The walk over q lands on q (the path with its
# entry), and the empty word after it changes nothing (LSp.sp_walk_gap:
# step.empty keeps a walk at a path), so both lines finish on the same
# state.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA
import ./base/space.bend as LSp

def Command.command_space_trailing(t, q, ok, on):
  match q:
    case Nil{}:
      LLogicLogic.cb_absurd({Cmd.resolve(t, List.append(&2, Nat, Command.cmd_render(Nil{}), [32n])) == Cmd.resolve(t, Command.cmd_render(Nil{})) : Cmd.Res}, on)
    case Con{+x, +rest}:
      +k = ok
      +o = on
      +hs = LA.cb_names_spaceless(x <> rest, LA.cb_walks_names(t, x <> rest, k, o))
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(List.append(&2, Nat, Command.cmd_render(x <> rest), [32n])), x <> List.append(&2, List<&2, Nat>, rest, [Nil{}]), LSp.sp_words_render(x, rest, [32n], [Nil{}], hs, {==})) : {Cmd.finish(Cmd.walk(_, t, Cmd.Top{}), t) == Cmd.resolve(t, Command.cmd_render(x <> rest)) : Cmd.Res}
      %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, x <> rest, [Nil{}]), t, Cmd.Top{}), Cmd.walk(List.append(&2, List<&2, Nat>, x <> rest, Nil{}), t, Cmd.Top{}), LSp.sp_walk_gap(t, x <> rest, Nil{}, k, o)) : {Cmd.finish(_, t) == Cmd.resolve(t, Command.cmd_render(x <> rest)) : Cmd.Res}
      %Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, x <> rest, Nil{}), x <> rest, LA.cb_app_nil(List<&2, Nat>, x <> rest)) : {Cmd.finish(Cmd.walk(_, t, Cmd.Top{}), t) == Cmd.resolve(t, Command.cmd_render(x <> rest)) : Cmd.Res}
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(Command.cmd_render(x <> rest)), x <> rest, LA.cb_words_render(x, rest, hs)) : {Cmd.finish(Cmd.walk(x <> rest, t, Cmd.Top{}), t) == Cmd.finish(Cmd.walk(_, t, Cmd.Top{}), t) : Cmd.Res}
      {==}
