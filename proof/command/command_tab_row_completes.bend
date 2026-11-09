# eukhe: the proof of LAW command_tab_row_completes
#
# PROOF of LAW command_tab_row_completes: the line keyed below q answers
# Tab through the row of the selection at q (KB.kb_key); place i holds e,
# a child of q, so the row is e (LA.kr_hit) and Tab answers key.tab on e:
# e's path (join is cmd_render), a space when e has a child (kids.any is
# cmd_has_kid) or expects text, the menu open when it has a child, no
# submit. In a well-formed table e's names are names (KB.kb_wf_get), so
# e's line ends in no space (KB.kb_es_kid), which fixes its shape
# (KB.kb_shape).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base.bend as LA
import ./base/keys.bend as KB

def tr_line(e: Cmd.Ent, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, hn: {Command.cmd_names_ok(Command.cmd_ent_path(e)) == True{} : Bool}, child: {Command.cmd_is_kid(q, Command.cmd_ent_path(e)) == True{} : Bool}) -> {CommandNamed.cmd_out_shape(Cmd.key.tab(Cmd.kids.any(t, Cmd.Ent.path(e)), Cmd.Ent.arg(e), Cmd.join(Cmd.Ent.path(e)))) == (List.append(&2, Nat, Command.cmd_render(Command.cmd_ent_path(e)), [32n]), (Bool.or(Command.cmd_has_kid(t, Command.cmd_ent_path(e)), CommandNamed.cmd_ent_arg(e)), (Command.cmd_has_kid(t, Command.cmd_ent_path(e)), False{}))) : List<&2, Nat> & (Bool & (Bool & Bool))}:
  match e:
    case Cmd.Ent{+pp, a, r, f, +g}:
      +K = Cmd.kids.any(t, pp)
      %LA.cb_kids_any(t, pp) : {CommandNamed.cmd_out_shape(Cmd.key.tab(K, g, Cmd.join(pp))) == (List.append(&2, Nat, Command.cmd_render(pp), [32n]), (Bool.or(_, g), (_, False{}))) : List<&2, Nat> & (Bool & (Bool & Bool))}
      %Equal.sym(List<&2, Nat>, Cmd.join(pp), Command.cmd_render(pp), LA.cb_join(pp)) : {CommandNamed.cmd_out_shape(Cmd.key.tab(K, g, _)) == (List.append(&2, Nat, Command.cmd_render(pp), [32n]), (Bool.or(K, g), (K, False{}))) : List<&2, Nat> & (Bool & (Bool & Bool))}
      KB.kb_shape(Bool.or(K, g), Command.cmd_render(pp), K, KB.kb_es_kid(q, pp, hn, child))

def CommandNamed.command_tab_row_completes(t, pre, p, q, i, e, ok, word, below, at, child):
  +L = List.append(&2, Nat, pre, p)
  +A = at
  +C = child
  -R = {(List.append(&2, Nat, Command.cmd_render(Command.cmd_ent_path(e)), [32n]), (Bool.or(Command.cmd_has_kid(t, Command.cmd_ent_path(e)), CommandNamed.cmd_ent_arg(e)), (Command.cmd_has_kid(t, Command.cmd_ent_path(e)), False{}))) : List<&2, Nat> & (Bool & (Bool & Bool))}
  %Equal.sym(Cmd.Out, Cmd.key(t, L, Cmd.Row{i}, Cmd.Tab{}), Cmd.key.row(Cmd.row(Cmd.Row{i}, t, q), Cmd.Tab{}, t, L, p), KB.kb_key(t, pre, p, q, Cmd.Row{i}, Cmd.Tab{}, word, below)) : {CommandNamed.cmd_out_shape(_) == R : List<&2, Nat> & (Bool & (Bool & Bool))}
  %LA.kr_hit(t, q, i, e, A, C) : {CommandNamed.cmd_out_shape(Cmd.key.row(_, Cmd.Tab{}, t, L, p)) == R : List<&2, Nat> & (Bool & (Bool & Bool))}
  tr_line(e, t, q, KB.kb_wf_get(t, i, e, ok, A), C)
