# PROOF of LAW command_free_takes_rest: the words of the line are q, w
# and more (every word is spaceless); the walk over q lands on q with its
# entry (B.cb_walk_root); w names no child of q by its lowercase name nor
# by an alias, so the search finds none and, q taking text, the walk
# stands at Rest{q, [w]} (B.cb_line_miss); argument text takes every
# later word as it is (B.cb_walk_rest), and finishing runs q with the
# words joined by single spaces, which is their rendering (B.cb_join).

import Base
import ../LAWS.bend as Laws
import ../bend/command.bend as Cmd
import ./base.bend as B

def Laws.command_free_takes_rest(t, q, w, more, ok, on, open, word, after, miss):
  match q:
    case Nil{}:
      B.cb_absurd({Cmd.resolve(t, Laws.cmd_render(List.append(&2, List<&2, Nat>, Nil{}, w <> more))) == Cmd.Runs{Nil{}, Laws.cmd_render(w <> more)} : Cmd.Res}, on)
    case Con{+x, +rest}:
      +qq = {x <> rest : List<&2, List<&2, Nat>>}
      +wm = {w <> more : List<&2, List<&2, Nat>>}
      %B.cb_join(wm) : {Cmd.resolve(t, Laws.cmd_render(List.append(&2, List<&2, Nat>, qq, wm))) == Cmd.Runs{qq, _} : Cmd.Res}
      %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(Laws.cmd_render(List.append(&2, List<&2, Nat>, qq, wm))), t, Cmd.Top{}), Cmd.walk(more, t, B.cb_miss(t, qq, w)), B.cb_line_miss(t, qq, w, more, ok, on, word, after, miss)) : {Cmd.finish(_, t) == Cmd.Runs{qq, Cmd.join(wm)} : Cmd.Res}
      %Equal.sym(Bool, Laws.cmd_free(t, qq), True{}, open) : {Cmd.finish(Cmd.walk(more, t, Cmd.step.miss(_, qq, w)), t) == Cmd.Runs{qq, Cmd.join(wm)} : Cmd.Res}
      %Equal.sym(Cmd.St, Cmd.walk(more, t, Cmd.Rest{qq, [w]}), Cmd.Rest{qq, wm}, B.cb_walk_rest(more, t, qq, [w])) : {Cmd.finish(_, t) == Cmd.Runs{qq, Cmd.join(wm)} : Cmd.Res}
      {==}
