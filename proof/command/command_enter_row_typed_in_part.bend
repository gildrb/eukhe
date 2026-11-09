# eukhe: the proof of LAW command_enter_row_typed_in_part
#
# PROOF of LAW command_enter_row_typed_in_part: the line keyed below q
# answers Tab and Enter through the row of the selection at q (KB.kb_key);
# place i holds e, a child of q, so the row is e for both (LA.kr_hit). The
# word does not name e (the model's names is cmd_names: KB.kb_names), so
# Enter answers key.fresh, which is key.tab's answer submitted exactly when
# e has no child and expects no text (ep_fresh, case by case; kids.any is
# cmd_has_kid).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base.bend as LA
import ./base/keys.bend as KB

def ep_fresh(k: Bool, g: Bool, +l: List<&2, Nat>) -> {Cmd.key.fresh(k, g, l) == CommandNamed.cmd_resubmit(Cmd.key.tab(k, g, l), Bool.not(Bool.or(k, g))) : Cmd.Out}:
  match k g:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ep_pick(e: Cmd.Ent, +t: List<&2, Cmd.Ent>, +L: List<&2, Nat>, +p: List<&2, Nat>, part: {CommandNamed.cmd_names(Command.cmd_lower(p), e) == False{} : Bool}) -> {Cmd.key.pick(Cmd.Enter{}, e, t, L, p) == CommandNamed.cmd_resubmit(Cmd.key.pick(Cmd.Tab{}, e, t, L, p), Bool.not(Bool.or(Command.cmd_has_kid(t, Command.cmd_ent_path(e)), CommandNamed.cmd_ent_arg(e)))) : Cmd.Out}:
  match e:
    case Cmd.Ent{+pp, +a, +r, +f, +g}:
      +E = {Cmd.Ent{pp, a, r, f, g} : Cmd.Ent}
      +K = Cmd.kids.any(t, pp)
      +nm = Equal.trans(Bool, Cmd.names(Cmd.lows(p), E), CommandNamed.cmd_names(Command.cmd_lower(p), E), False{}, KB.kb_names(E, p), part)
      %Equal.sym(Bool, Cmd.names(Cmd.lows(p), E), False{}, nm) : {Cmd.key.row_enter(_, Cmd.done(t, E), K, g, Cmd.join(pp), L) == CommandNamed.cmd_resubmit(Cmd.key.tab(K, g, Cmd.join(pp)), Bool.not(Bool.or(Command.cmd_has_kid(t, pp), g))) : Cmd.Out}
      %LA.cb_kids_any(t, pp) : {Cmd.key.fresh(K, g, Cmd.join(pp)) == CommandNamed.cmd_resubmit(Cmd.key.tab(K, g, Cmd.join(pp)), Bool.not(Bool.or(_, g))) : Cmd.Out}
      ep_fresh(K, g, Cmd.join(pp))

def CommandNamed.command_enter_row_typed_in_part(t, pre, p, q, i, e, word, below, at, child, part):
  +L = List.append(&2, Nat, pre, p)
  +w = word
  +b = below
  +X = Bool.not(Bool.or(Command.cmd_has_kid(t, Command.cmd_ent_path(e)), CommandNamed.cmd_ent_arg(e)))
  %Equal.sym(Cmd.Out, Cmd.key(t, L, Cmd.Row{i}, Cmd.Enter{}), Cmd.key.row(Cmd.row(Cmd.Row{i}, t, q), Cmd.Enter{}, t, L, p), KB.kb_key(t, pre, p, q, Cmd.Row{i}, Cmd.Enter{}, w, b)) : {_ == CommandNamed.cmd_resubmit(Cmd.key(t, L, Cmd.Row{i}, Cmd.Tab{}), X) : Cmd.Out}
  %Equal.sym(Cmd.Out, Cmd.key(t, L, Cmd.Row{i}, Cmd.Tab{}), Cmd.key.row(Cmd.row(Cmd.Row{i}, t, q), Cmd.Tab{}, t, L, p), KB.kb_key(t, pre, p, q, Cmd.Row{i}, Cmd.Tab{}, w, b)) : {Cmd.key.row(Cmd.row(Cmd.Row{i}, t, q), Cmd.Enter{}, t, L, p) == CommandNamed.cmd_resubmit(_, X) : Cmd.Out}
  %LA.kr_hit(t, q, i, e, at, child) : {Cmd.key.row(_, Cmd.Enter{}, t, L, p) == CommandNamed.cmd_resubmit(Cmd.key.row(_, Cmd.Tab{}, t, L, p), X) : Cmd.Out}
  ep_pick(e, t, L, p, part)
