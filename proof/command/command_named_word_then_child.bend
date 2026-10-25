# eukhe: the proof of LAW command_named_word_then_child
#
# PROOF of LAW command_named_word_then_child: the canonical path is q and
# its last name y (nm_path), which names the first entry e1 of the path
# (nm_named_decl, nm_canon_hit); both lines walk onto the path (with e,
# with e1) before x (nm_walk_then), and from either entry x steps onto
# its child e2 (nm_step_of), so the rest walks alike.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base.bend as LA
import ./base/named.bend as LACommandNamed
import ../base/logic/bool.bend as LLogicBool

def CommandNamed.command_named_word_then_child(t, q, w, e, gs, n, x, e2, s, ok, on, word, hit, next, kid, gap):
  +ok2 = ok
  +on2 = on
  +hit2 = hit
  +next2 = next
  +kid2 = kid
  +gap2 = gap
  +pe = Command.cmd_ent_path(e)
  +y = Command.cmd_last(pe)
  +qy = List.append(&2, List<&2, Nat>, q, [y])
  +dP = LACommandNamed.nm_named_decl(t, q, w, e, hit2)
  +e1 = LACommandNamed.nm_first.of(Command.cmd_lookup(t, pe), dP)
  +first = LACommandNamed.nm_first.eq(Command.cmd_lookup(t, pe), dP)
  +ty = LLogicBool.cb_and_l(Command.cmd_typed(y), Command.cmd_eq(Command.cmd_lower(y), y), LACommandNamed.nm_canon_name(t, q, w, e, e1, ok2, hit2, first))
  +hy = LACommandNamed.nm_canon_hit(t, q, w, e, e1, ok2, hit2, first)
  +hx = LA.cb_typed_spaceless(x, next2)
  +Y = LACommandNamed.nm_tail(s)
  +p1 = Equal.trans(List<&2, List<&2, Nat>>, Cmd.Ent.path(e1), Cmd.Ent.path(e), pe, LACommandNamed.nm_first_path(t, e, e1, first), LA.cb_ent_path(e))
  %Equal.sym(List<&2, List<&2, Nat>>, pe, qy, LACommandNamed.nm_path(t, q, w, e, hit2)) : {Cmd.resolve(t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> List.append(&2, Nat, Command.cmd_spaces(n), List.append(&2, Nat, x, s)))) == Cmd.resolve(t, List.append(&2, Nat, Command.cmd_loose(_, gs), 32n <> List.append(&2, Nat, Command.cmd_spaces(n), List.append(&2, Nat, x, s)))) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> List.append(&2, Nat, Command.cmd_spaces(n), List.append(&2, Nat, x, s)))), t, Cmd.Top{}), Cmd.walk(Y, t, Cmd.step(Cmd.Walk{Cmd.Ent.path(e), e}, t, x)), LACommandNamed.nm_walk_then(t, q, w, e, gs, n, x, s, ok2, on2, word, hit2, hx, gap2)) : {Cmd.finish(_, t) == Cmd.resolve(t, List.append(&2, Nat, Command.cmd_loose(qy, gs), 32n <> List.append(&2, Nat, Command.cmd_spaces(n), List.append(&2, Nat, x, s)))) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(List.append(&2, Nat, Command.cmd_loose(qy, gs), 32n <> List.append(&2, Nat, Command.cmd_spaces(n), List.append(&2, Nat, x, s)))), t, Cmd.Top{}), Cmd.walk(Y, t, Cmd.step(Cmd.Walk{Cmd.Ent.path(e1), e1}, t, x)), LACommandNamed.nm_walk_then(t, q, y, e1, gs, n, x, s, ok2, on2, ty, hy, hx, gap2)) : {Cmd.finish(Cmd.walk(Y, t, Cmd.step(Cmd.Walk{Cmd.Ent.path(e), e}, t, x)), t) == Cmd.finish(_, t) : Cmd.Res}
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.Ent.path(e), pe, LA.cb_ent_path(e)) : {Cmd.finish(Cmd.walk(Y, t, Cmd.step(Cmd.Walk{_, e}, t, x)), t) == Cmd.finish(Cmd.walk(Y, t, Cmd.step(Cmd.Walk{Cmd.Ent.path(e1), e1}, t, x)), t) : Cmd.Res}
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.Ent.path(e1), pe, p1) : {Cmd.finish(Cmd.walk(Y, t, Cmd.step(Cmd.Walk{pe, e}, t, x)), t) == Cmd.finish(Cmd.walk(Y, t, Cmd.step(Cmd.Walk{_, e1}, t, x)), t) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.step(Cmd.Walk{pe, e}, t, x), Cmd.Walk{Cmd.Ent.path(e2), e2}, LACommandNamed.nm_step_of(Some{e}, t, pe, x, e2, {==}, next2, kid2)) : {Cmd.finish(Cmd.walk(Y, t, _), t) == Cmd.finish(Cmd.walk(Y, t, Cmd.step(Cmd.Walk{pe, e1}, t, x)), t) : Cmd.Res}
  %Equal.sym(Cmd.St, Cmd.step(Cmd.Walk{pe, e1}, t, x), Cmd.Walk{Cmd.Ent.path(e2), e2}, LACommandNamed.nm_step_of(Some{e1}, t, pe, x, e2, {==}, next2, kid2)) : {Cmd.finish(Cmd.walk(Y, t, Cmd.Walk{Cmd.Ent.path(e2), e2}), t) == Cmd.finish(Cmd.walk(Y, t, _), t) : Cmd.Res}
  {==}
