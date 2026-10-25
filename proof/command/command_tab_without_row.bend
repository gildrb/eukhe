# eukhe: the proof of LAW command_tab_without_row
#
# PROOF of LAW command_tab_without_row: with no row, every walk state
# answers Tab through key.bare (the root and a walk find no row to pick,
# the other states go to key.bare directly), and key.bare on Tab keeps
# the line and opens its menu; so Tab is the same whatever the line cuts
# into.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command

# at any walk state, Tab with no row keeps the line and opens the menu
def ktwr.at(s: Cmd.St, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, p: List<&2, Nat>) -> {Cmd.key.at(s, t, line, p, Cmd.NoRow{}, Cmd.Tab{}) == Cmd.Out{line, True{}, False{}} : Cmd.Out}:
  match s:
    case Cmd.Top{}:
      {==}
    case Cmd.Walk{q, e}:
      {==}
    case Cmd.Rest{q, ws}:
      {==}
    case Cmd.Lost{q, w}:
      {==}
    case Cmd.Stray{}:
      {==}

# whatever the line cuts into
def ktwr.cut(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>) -> {Cmd.key.cut(c, t, line, Cmd.NoRow{}, Cmd.Tab{}) == Cmd.Out{line, True{}, False{}} : Cmd.Out}:
  match c:
    case (d, p):
      ktwr.at(Cmd.walk(d, t, Cmd.Top{}), t, line, p)

def Command.command_tab_without_row(t, line):
  ktwr.cut(Cmd.cut(Cmd.words(line)), t, line)
