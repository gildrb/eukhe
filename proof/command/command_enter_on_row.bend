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
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def eor_typed(d: Bool, l: List<&2, Nat>, line: List<&2, Nat>) -> {Cmd.key.typed(d, l, line) == Laws.cmd_enter.typed(d, l, line) : Cmd.Out}:
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

def eor_fresh(k: Bool, g: Bool, l: List<&2, Nat>) -> {Cmd.key.fresh(k, g, l) == Laws.cmd_enter.fresh(k, g, l) : Cmd.Out}:
  match k g:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def eor_at(full: Bool, +k: Bool, r: Bool, g: Bool, l: List<&2, Nat>, line: List<&2, Nat>) -> {Cmd.key.row_enter(full, Bool.or(r, Bool.not(k)), k, g, l, line) == Laws.cmd_enter.at(full, k, r, g, l, line) : Cmd.Out}:
  match full:
    case True{}:
      eor_typed(Bool.or(r, Bool.not(k)), l, line)
    case False{}:
      eor_fresh(k, g, l)

# Enter on the row e is cmd_enter
def eor_pick(e: Cmd.Ent, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, +p: List<&2, Nat>) -> {Cmd.key.pick(Cmd.Enter{}, e, t, line, p) == Laws.cmd_enter(t, e, p, line) : Cmd.Out}:
  match e:
    case Cmd.Ent{+pp, +a, +r, f, +g}:
      %LA.cb_lows(p) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Laws.cmd_enter.at(Bool.or(Laws.cmd_eq(_, Laws.cmd_last(pp)), Laws.cmd_in(_, a)), Laws.cmd_has_kid(t, pp), r, g, Laws.cmd_render(pp), line) : Cmd.Out}
      %LA.cb_last(pp) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Laws.cmd_enter.at(Bool.or(Laws.cmd_eq(Cmd.lows(p), _), Laws.cmd_in(Cmd.lows(p), a)), Laws.cmd_has_kid(t, pp), r, g, Laws.cmd_render(pp), line) : Cmd.Out}
      %L.cb_same(Cmd.lows(p), Cmd.last(pp)) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Laws.cmd_enter.at(Bool.or(_, Laws.cmd_in(Cmd.lows(p), a)), Laws.cmd_has_kid(t, pp), r, g, Laws.cmd_render(pp), line) : Cmd.Out}
      %LA.cb_has(a, Cmd.lows(p)) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Laws.cmd_enter.at(Bool.or(Cmd.same(Cmd.lows(p), Cmd.last(pp)), _), Laws.cmd_has_kid(t, pp), r, g, Laws.cmd_render(pp), line) : Cmd.Out}
      %LA.cb_kids_any(t, pp) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Laws.cmd_enter.at(Bool.or(Cmd.same(Cmd.lows(p), Cmd.last(pp)), Cmd.has(a, Cmd.lows(p))), _, r, g, Laws.cmd_render(pp), line) : Cmd.Out}
      %LA.cb_join(pp) : {Cmd.key.pick(Cmd.Enter{}, Cmd.Ent{pp, a, r, f, g}, t, line, p) == Laws.cmd_enter.at(Bool.or(Cmd.same(Cmd.lows(p), Cmd.last(pp)), Cmd.has(a, Cmd.lows(p))), Cmd.kids.any(t, pp), r, g, _, line) : Cmd.Out}
      eor_at(Bool.or(Cmd.same(Cmd.lows(p), Cmd.last(pp)), Cmd.has(a, Cmd.lows(p))), Cmd.kids.any(t, pp), r, g, Cmd.join(pp), line)

def Laws.command_enter_on_row(t, q, p, i, e, ok, on, word, at, child):
  %LA.kr_key(t, q, p, Cmd.Row{i}, Cmd.Enter{}, ok, on, word) : {_ == Laws.cmd_enter(t, e, p, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p]))) : Cmd.Out}
  %LA.kr_hit(t, q, i, e, at, child) : {Cmd.key.row(_, Cmd.Enter{}, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == Laws.cmd_enter(t, e, p, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p]))) : Cmd.Out}
  eor_pick(e, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p)
