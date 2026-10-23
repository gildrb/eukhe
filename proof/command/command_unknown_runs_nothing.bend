# eukhe: the proof of LAW command_unknown_runs_nothing
#
# PROOF of LAW command_unknown_runs_nothing: the words of the line are q,
# w and more (every word is spaceless); the walk over q lands on q with
# its entry (B.cb_walk_root); w names no child of q by its lowercase name
# (q ++ [lower w] is not declared) nor by an alias, so the search finds
# none and, q taking no text, the walk stands at Lost{q, w}
# (B.cb_line_miss); an unknown word stays whatever follows
# (B.cb_walk_lost) and finishes as Unknown{q, w}.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command.bend as Command
import ../base/bool/misc.bend as LBoolMisc
import ./base.bend as LA

def Command.command_unknown_runs_nothing(t, q, w, more, ok, on, shut, word, after, miss):
  match q:
    case Nil{}:
      LBoolMisc.cb_absurd({Cmd.resolve(t, Command.cmd_render(List.append(&2, List<&2, Nat>, Nil{}, w <> more))) == Cmd.Unknown{Nil{}, w} : Cmd.Res}, on)
    case Con{+x, +rest}:
      +qq = {x <> rest : List<&2, List<&2, Nat>>}
      %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(Command.cmd_render(List.append(&2, List<&2, Nat>, qq, w <> more))), t, Cmd.Top{}), Cmd.walk(more, t, LA.cb_miss(t, qq, w)), LA.cb_line_miss(t, qq, w, more, ok, on, word, after, miss)) : {Cmd.finish(_, t) == Cmd.Unknown{qq, w} : Cmd.Res}
      %Equal.sym(Bool, Command.cmd_free(t, qq), False{}, shut) : {Cmd.finish(Cmd.walk(more, t, Cmd.step.miss(_, qq, w)), t) == Cmd.Unknown{qq, w} : Cmd.Res}
      %Equal.sym(Cmd.St, Cmd.walk(more, t, Cmd.Lost{qq, w}), Cmd.Lost{qq, w}, LA.cb_walk_lost(more, t, qq, w)) : {Cmd.finish(_, t) == Cmd.Unknown{qq, w} : Cmd.Res}
      {==}
