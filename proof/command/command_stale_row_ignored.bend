# eukhe: the proof of LAW command_stale_row_ignored
#
# PROOF of LAW command_stale_row_ignored: the line q p cuts into the
# words of q and the last word p, and the walk over q from the root
# stands at q (the root, or a walk at q); there key.at answers through
# key.row on the row of the selection at q (kr_key, shared with the
# other row laws). A place that holds no child of q (past the table, or
# an entry whose path is not q and one name) gives no row: row.of is
# None, the same as no selection.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command.bend as Command
import ./base.bend as LA

# a place whose entry is no child of q gives no row
def kr_miss_kid(e: Cmd.Ent, +q: List<&2, List<&2, Nat>>, s: {Command.cmd_is_kid(q, Command.cmd_ent_path(e)) == False{} : Bool}) -> {None{} == Cmd.row.kid(Cmd.kid(q, Cmd.Ent.path(e)), e) : Maybe<&2, Cmd.Ent>}:
  match e:
    case Cmd.Ent{+pp, a, r, f, g}:
      %Equal.sym(Bool, Cmd.kid(q, pp), Command.cmd_is_kid(q, pp), LA.cb_kid(q, pp)) : {None{} == Cmd.row.kid(_, Cmd.Ent{pp, a, r, f, g}) : Maybe<&2, Cmd.Ent>}
      %Equal.sym(Bool, Command.cmd_is_kid(q, pp), False{}, s) : {None{} == Cmd.row.kid(_, Cmd.Ent{pp, a, r, f, g}) : Maybe<&2, Cmd.Ent>}
      {==}

def kr_miss_of(m: Maybe<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, s: {Command.cmd_row.of(m, q) == False{} : Bool}) -> {None{} == Cmd.row.of(m, q) : Maybe<&2, Cmd.Ent>}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      kr_miss_kid(e, q, s)

def Command.command_stale_row_ignored(t, q, p, i, k, ok, on, word, stale):
  +o = ok
  +n = on
  +w = word
  %LA.kr_key(t, q, p, Cmd.Row{i}, k, o, n, w) : {_ == Cmd.key(t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), Cmd.NoRow{}, k) : Cmd.Out}
  %LA.kr_key(t, q, p, Cmd.NoRow{}, k, o, n, w) : {Cmd.key.row(Cmd.row(Cmd.Row{i}, t, q), k, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == _ : Cmd.Out}
  %kr_miss_of(List.get(&2, Cmd.Ent, t, i), q, stale) : {Cmd.key.row(_, k, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == Cmd.key.row(None{}, k, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) : Cmd.Out}
  {==}
