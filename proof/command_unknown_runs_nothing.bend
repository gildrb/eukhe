# PROOF of LAW command_unknown_runs_nothing: the words of the line are q,
# w and more (every word is spaceless); the walk over q lands on q with
# its entry (B.cb_walk_root); w names no child of q by its lowercase name
# (q ++ [lower w] is not declared) nor by an alias, so the search finds
# none and, q taking no text, the walk stands at Lost{q, w}
# (B.cb_line_miss); an unknown word stays whatever follows
# (B.cb_walk_lost) and finishes as Unknown{q, w}.

import Base
import ../LAWS.bend as Laws
import ../bend/command.bend as Cmd
import ./base.bend as B

def Laws.command_unknown_runs_nothing(t, q, w, more, ok, on, shut, word, after, miss):
  match q:
    case Nil{}:
      B.cb_absurd({Cmd.resolve(t, Laws.cmd_render(List.append(&2, List<&2, Nat>, Nil{}, w <> more))) == Cmd.Unknown{Nil{}, w} : Cmd.Res}, on)
    case Con{+x, +rest}:
      +qq = {x <> rest : List<&2, List<&2, Nat>>}
      %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(Laws.cmd_render(List.append(&2, List<&2, Nat>, qq, w <> more))), t, Cmd.Top{}), Cmd.walk(more, t, B.cb_miss(t, qq, w)), B.cb_line_miss(t, qq, w, more, ok, on, word, after, miss)) : {Cmd.finish(_, t) == Cmd.Unknown{qq, w} : Cmd.Res}
      %Equal.sym(Bool, Laws.cmd_free(t, qq), False{}, shut) : {Cmd.finish(Cmd.walk(more, t, Cmd.step.miss(_, qq, w)), t) == Cmd.Unknown{qq, w} : Cmd.Res}
      %Equal.sym(Cmd.St, Cmd.walk(more, t, Cmd.Lost{qq, w}), Cmd.Lost{qq, w}, B.cb_walk_lost(more, t, qq, w)) : {Cmd.finish(_, t) == Cmd.Unknown{qq, w} : Cmd.Res}
      {==}
