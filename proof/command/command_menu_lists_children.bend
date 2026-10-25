# eukhe: the proof of LAW command_menu_lists_children
#
# PROOF of LAW command_menu_lists_children: the words of the line are the
# names of q and then p (every word is spaceless), so the cut is (q, p)
# (B.cb_cut_last); the walk over q lands on q with its entry
# (B.cb_walk_root), whose menu is the rows of the children of q that
# start with the lowercase of p, which is cmd_rows (B.cb_items, B.cb_lows).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../base/list.bend as LList
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# the model's starts is cmd_prefix
def cb_starts(x: List<&2, Nat>, n: List<&2, Nat>) -> {Cmd.starts(x, n) == Command.cmd_prefix(x, n) : Bool}:
  match x n:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      {==}
    case Con{a, as} Nil{}:
      {==}
    case Con{+a, +as} Con{+y, +ys}:
      %cb_starts(as, ys) : {Bool.and(Nat.is_eq(a, y), Cmd.starts(as, ys)) == Bool.and(Nat.is_eq(a, y), _) : Bool}
      {==}

# the model's has_start is cmd_prefix_in
def cb_has_start(xs: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Cmd.has_start(xs, x) == Command.cmd_prefix_in(x, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %cb_has_start(rest, x) : {Bool.or(Cmd.starts(x, y), Cmd.has_start(rest, x)) == Bool.or(Command.cmd_prefix(x, y), _) : Bool}
      %cb_starts(x, y) : {Bool.or(Cmd.starts(x, y), Cmd.has_start(rest, x)) == Bool.or(_, Cmd.has_start(rest, x)) : Bool}
      {==}

def cb_items_at(b: Bool, -i: Nat, -r: List<&2, Nat>) -> {Cmd.items.at(b, i, r) == Command.cmd_rows.at(b, i, r) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cb_row_cond(+q: List<&2, List<&2, Nat>>, +p: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) == Bool.and(Command.cmd_is_kid(q, p), Bool.or(Command.cmd_prefix(x, Command.cmd_last(p)), Command.cmd_prefix_in(x, a))) : Bool}:
  %cb_has_start(a, x) : {Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) == Bool.and(Command.cmd_is_kid(q, p), Bool.or(Command.cmd_prefix(x, Command.cmd_last(p)), _)) : Bool}
  %LA.cb_last(p) : {Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) == Bool.and(Command.cmd_is_kid(q, p), Bool.or(Command.cmd_prefix(x, _), Cmd.has_start(a, x))) : Bool}
  %cb_starts(x, Cmd.last(p)) : {Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) == Bool.and(Command.cmd_is_kid(q, p), Bool.or(_, Cmd.has_start(a, x))) : Bool}
  %LA.cb_kid(q, p) : {Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) == Bool.and(_, Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) : Bool}
  {==}

# the model's items is cmd_rows
def cb_items(t: List<&2, Cmd.Ent>, +i: Nat, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Cmd.items(t, i, q, x) == Command.cmd_rows(t, i, q, x) : List<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{Cmd.Ent{+p, +a, r, f, g}, +rest}:
      %cb_items(rest, 1n+i, q, x) : {Cmd.items.at(Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))), i, Cmd.items(rest, 1n+i, q, x)) == Command.cmd_rows.at(Bool.and(Command.cmd_is_kid(q, p), Bool.or(Command.cmd_prefix(x, Command.cmd_last(p)), Command.cmd_prefix_in(x, a))), i, _) : List<&2, Nat>}
      %cb_row_cond(q, p, a, x) : {Cmd.items.at(Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))), i, Cmd.items(rest, 1n+i, q, x)) == Command.cmd_rows.at(_, i, Cmd.items(rest, 1n+i, q, x)) : List<&2, Nat>}
      cb_items_at(Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))), i, Cmd.items(rest, 1n+i, q, x))

def pml_at(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, hs: {Command.cmd_some(m) == True{} : Bool}) -> {Cmd.menu.at(LA.cb_st.of(m, q), t, p) == Cmd.Kids{q, Cmd.items(t, 0n, q, Cmd.lows(p))} : Cmd.Menu}:
  match m:
    case None{}:
      LLogicLogic.cb_absurd({Cmd.menu.at(LA.cb_st.of(None{}, q), t, p) == Cmd.Kids{q, Cmd.items(t, 0n, q, Cmd.lows(p))} : Cmd.Menu}, hs)
    case Some{e}:
      {==}

def Command.command_menu_lists_children(t, q, p, ok, on, word):
  match q:
    case Nil{}:
      LLogicLogic.cb_absurd({Cmd.menu(t, Command.cmd_render(List.append(&2, List<&2, Nat>, Nil{}, [p]))) == Cmd.Kids{Nil{}, Command.cmd_rows(t, 0n, Nil{}, Command.cmd_lower(p))} : Cmd.Menu}, on)
    case Con{+x, +rest}:
      +qq = {x <> rest : List<&2, List<&2, Nat>>}
      +o = on
      +k = ok
      +line = Command.cmd_render(List.append(&2, List<&2, Nat>, qq, [p]))
      %cb_items(t, 0n, qq, Command.cmd_lower(p)) : {Cmd.menu(t, line) == Cmd.Kids{qq, _} : Cmd.Menu}
      %LA.cb_lows(p) : {Cmd.menu(t, line) == Cmd.Kids{qq, Cmd.items(t, 0n, qq, _)} : Cmd.Menu}
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(Cmd.words(line)), (qq, p), LA.cb_cut_last(t, qq, p, k, o, word)) : {Cmd.menu.cut(_, t) == Cmd.Kids{qq, Cmd.items(t, 0n, qq, Cmd.lows(p))} : Cmd.Menu}
      %Equal.sym(Cmd.St, Cmd.walk(qq, t, Cmd.Top{}), LA.cb_st(t, qq), LA.cb_walk_root(qq, t, k, o)) : {Cmd.menu.at(_, t, p) == Cmd.Kids{qq, Cmd.items(t, 0n, qq, Cmd.lows(p))} : Cmd.Menu}
      pml_at(Command.cmd_lookup(t, qq), t, qq, p, LList.cb_walks_decl(rest, x, t, Nil{}, o))
