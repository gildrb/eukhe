# PROOF of LAW command_stray_is_not_a_command: the words of the line are w
# and more (every word is spaceless); at the root, w names no command by
# its lowercase name ([lower w] is not declared) nor by an alias, so the
# search finds none and the walk stands at Stray (B.cb_step_miss); a
# stray first word stays whatever follows (B.cb_walk_stray) and finishes
# as no command.

import Base
import ../LAWS.bend as Laws
import ../bend/command.bend as Cmd
import ./base.bend as B

def Laws.command_stray_is_not_a_command(t, w, more, word, after, miss):
  +k = word
  +hs = B.cb_and_intro(Laws.cmd_spaceless(w), Laws.cmd_all_spaceless(more), B.cb_typed_spaceless(w, k), after)
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(Laws.cmd_render(w <> more)), w <> more, B.cb_words_render(w, more, hs)) : {Cmd.finish(Cmd.walk(_, t, Cmd.Top{}), t) == Cmd.NoCmd{} : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.step(Cmd.Top{}, t, w), Cmd.Stray{}, B.cb_step_miss(t, Nil{}, w, {==}, k, miss)) : {Cmd.finish(Cmd.walk(more, t, _), t) == Cmd.NoCmd{} : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.walk(more, t, Cmd.Stray{}), Cmd.Stray{}, B.cb_walk_stray(more, t)) : {Cmd.finish(_, t) == Cmd.NoCmd{} : Cmd.Res}
  {==}
