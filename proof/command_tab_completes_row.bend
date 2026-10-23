# PROOF of LAW command_tab_completes_row: the line q p answers through
# the row of the selection at q (KR.kr_key); the place i holds e, a
# child of q, so the row is e and Tab picks it (KR.kr_hit). key.tab on e
# and cmd_tab agree: kids.any is cmd_has_kid, join is cmd_render, and
# spaced is cmd_space_if.

import Base
import ../LAWS.bend as Laws
import ../bend/command.bend as Cmd
import ./base.bend as B
import ./command_stale_row_ignored.bend as KR

def tcr_spaced(b: Bool, l: List<&2, Nat>) -> {Cmd.spaced(b, l) == Laws.cmd_space_if(b, l) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Tab on the row e is cmd_tab
def tcr_pick(e: Cmd.Ent, +t: List<&2, Cmd.Ent>, line: List<&2, Nat>, p: List<&2, Nat>) -> {Cmd.key.pick(Cmd.Tab{}, e, t, line, p) == Laws.cmd_tab(t, e) : Cmd.Out}:
  match e:
    case Cmd.Ent{+pp, a, r, f, +g}:
      %B.cb_kids_any(t, pp) : {Cmd.Out{Cmd.spaced(Bool.or(Cmd.kids.any(t, pp), g), Cmd.join(pp)), Cmd.kids.any(t, pp), False{}} == Cmd.Out{Laws.cmd_space_if(Bool.or(_, g), Laws.cmd_render(pp)), _, False{}} : Cmd.Out}
      %B.cb_join(pp) : {Cmd.Out{Cmd.spaced(Bool.or(Cmd.kids.any(t, pp), g), Cmd.join(pp)), Cmd.kids.any(t, pp), False{}} == Cmd.Out{Laws.cmd_space_if(Bool.or(Cmd.kids.any(t, pp), g), _), Cmd.kids.any(t, pp), False{}} : Cmd.Out}
      %tcr_spaced(Bool.or(Cmd.kids.any(t, pp), g), Cmd.join(pp)) : {Cmd.Out{Cmd.spaced(Bool.or(Cmd.kids.any(t, pp), g), Cmd.join(pp)), Cmd.kids.any(t, pp), False{}} == Cmd.Out{_, Cmd.kids.any(t, pp), False{}} : Cmd.Out}
      {==}

def Laws.command_tab_completes_row(t, q, p, i, e, ok, on, word, at, child):
  %KR.kr_key(t, q, p, Cmd.Row{i}, Cmd.Tab{}, ok, on, word) : {_ == Laws.cmd_tab(t, e) : Cmd.Out}
  %KR.kr_hit(t, q, i, e, at, child) : {Cmd.key.row(_, Cmd.Tab{}, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == Laws.cmd_tab(t, e) : Cmd.Out}
  tcr_pick(e, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p)
