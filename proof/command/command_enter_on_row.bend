# eukhe: the proof of LAW command_enter_on_row
#
# PROOF of LAW command_enter_on_row: the line q p answers through the
# row of the selection at q (KR.kr_key); the place i holds e, a child of
# q, so the row is e and Enter picks it (KR.kr_hit). key.row_enter on e
# and cmd_enter agree: the typed word names e (names of lows) is
# cmd_eq/cmd_in of cmd_lower against cmd_last and the aliases, done is
# a default or no child (kids.any is cmd_has_kid), join is cmd_render;
# the typed and fresh answers then agree case by case.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../base/command.bend as LCommand
import ./base.bend as LA

def eor_typed(d: Bool, l: List<&2, Nat>, line: List<&2, Nat>) -> {Cmd.key.typed(d, l, line) == Command.cmd_enter.typed(d, l, line) : Cmd.Out}:
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

def eor_fresh(k: Bool, g: Bool, l: List<&2, Nat>) -> {Cmd.key.fresh(k, g, l) == Command.cmd_enter.fresh(k, g, l) : Cmd.Out}:
  match k g:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def eor_at(full: Bool, +k: Bool, r: Bool, g: Bool, l: List<&2, Nat>, line: List<&2, Nat>) -> {Cmd.key.row_enter(full, Bool.or(r, Bool.not(k)), k, g, l, line) == Command.cmd_enter.at(full, k, r, g, l, line) : Cmd.Out}:
  match full:
    case True{}:
      eor_typed(Bool.or(r, Bool.not(k)), l, line)
    case False{}:
      eor_fresh(k, g, l)

# Enter on the row e is cmd_enter
def eor_pick(e: Cmd.Ent, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, +p: List<&2, Nat>) -> {Cmd.key.pick(Cmd.Enter{}, e, t, line, p) == Command.cmd_enter(t, e, p, line) : Cmd.Out}:
  match e:
    case Cmd.Ent{+pp, +a, +r, f, +g}:
      %LA.cb_lows(p) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Command.cmd_enter.at(Bool.or(Command.cmd_eq(_, Command.cmd_last(pp)), Command.cmd_in(_, a)), Command.cmd_has_kid(t, pp), r, g, Command.cmd_render(pp), line) : Cmd.Out}
      %LA.cb_last(pp) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Command.cmd_enter.at(Bool.or(Command.cmd_eq(Cmd.lows(p), _), Command.cmd_in(Cmd.lows(p), a)), Command.cmd_has_kid(t, pp), r, g, Command.cmd_render(pp), line) : Cmd.Out}
      %LCommand.cb_same(Cmd.lows(p), Cmd.last(pp)) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Command.cmd_enter.at(Bool.or(_, Command.cmd_in(Cmd.lows(p), a)), Command.cmd_has_kid(t, pp), r, g, Command.cmd_render(pp), line) : Cmd.Out}
      %LA.cb_has(a, Cmd.lows(p)) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Command.cmd_enter.at(Bool.or(Cmd.same(Cmd.lows(p), Cmd.last(pp)), _), Command.cmd_has_kid(t, pp), r, g, Command.cmd_render(pp), line) : Cmd.Out}
      %LA.cb_kids_any(t, pp) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Command.cmd_enter.at(Bool.or(Cmd.same(Cmd.lows(p), Cmd.last(pp)), Cmd.has(a, Cmd.lows(p))), _, r, g, Command.cmd_render(pp), line) : Cmd.Out}
      %LA.cb_join(pp) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Command.cmd_enter.at(Bool.or(Cmd.same(Cmd.lows(p), Cmd.last(pp)), Cmd.has(a, Cmd.lows(p))), Cmd.kids.any(t, pp), r, g, _, line) : Cmd.Out}
      eor_at(Bool.or(Cmd.same(Cmd.lows(p), Cmd.last(pp)), Cmd.has(a, Cmd.lows(p))), Cmd.kids.any(t, pp), r, g, Cmd.join(pp), line)

def Command.command_enter_on_row(t, q, p, i, e, ok, on, word, at, child):
  %LA.kr_key(t, q, p, Cmd.Row{i}, Cmd.Enter{}, ok, on, word) : {_ == Command.cmd_enter(t, e, p, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p]))) : Cmd.Out}
  %LA.kr_hit(t, q, i, e, at, child) : {Cmd.key.row(_, Cmd.Enter{}, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == Command.cmd_enter(t, e, p, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p]))) : Cmd.Out}
  eor_pick(e, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p)
