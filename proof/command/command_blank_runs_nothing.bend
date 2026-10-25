# eukhe: the proof of LAW command_blank_runs_nothing
#
# PROOF of LAW command_blank_runs_nothing: by induction on the line: the
# empty line is one empty word, which leaves the walk at the root; a
# space before a blank line adds an empty word first, which leaves the
# walk at the root too; the root finishes as no command.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/named.bend as CommandNamed
import ../base/logic/logic.bend as LLogicLogic

def cbr_at(b: Bool, +c: Nat, +r: List<&2, Nat>, +t: List<&2, Cmd.Ent>, hb: {Bool.and(b, CommandNamed.cmd_blank(r)) == True{} : Bool}, ih: {CommandNamed.cmd_blank(r) == True{} : Bool} -> {Cmd.finish(Cmd.walk(Cmd.words(r), t, Cmd.Top{}), t) == Cmd.NoCmd{} : Cmd.Res}) -> {Cmd.finish(Cmd.walk(Cmd.words.at(b, c, Cmd.words(r)), t, Cmd.Top{}), t) == Cmd.NoCmd{} : Cmd.Res}:
  match b:
    case True{}:
      ih(hb)
    case False{}:
      LLogicLogic.cb_absurd({Cmd.finish(Cmd.walk(Cmd.words.at(False{}, c, Cmd.words(r)), t, Cmd.Top{}), t) == Cmd.NoCmd{} : Cmd.Res}, hb)

def CommandNamed.command_blank_runs_nothing(t, line, blank):
  match line:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      cbr_at(Nat.is_eq(c, 32n), c, r, t, blank, x => CommandNamed.command_blank_runs_nothing(t, r, x))
