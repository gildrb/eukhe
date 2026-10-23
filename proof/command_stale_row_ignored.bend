# PROOF of LAW command_stale_row_ignored: the line q p cuts into the
# words of q and the last word p, and the walk over q from the root
# stands at q (the root, or a walk at q); there key.at answers through
# key.row on the row of the selection at q (kr_key, shared with the
# other row laws). A place that holds no child of q (past the table, or
# an entry whose path is not q and one name) gives no row: row.of is
# None, the same as no selection.

import Base
import ../LAWS.bend as Laws
import ../bend/command.bend as Cmd
import ./base.bend as B

# a walk at a declared path q answers through the row of the selection
# at q
def kr_st_of(m: Maybe<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, s: {Laws.cmd_some(m) == True{} : Bool}) -> {Cmd.key.row(Cmd.row(sel, t, q), k, t, line, p) == Cmd.key.at(B.cb_st.of(m, q), t, line, p, sel, k) : Cmd.Out}:
  match m:
    case None{}:
      B.cb_absurd({Cmd.key.row(Cmd.row(sel, t, q), k, t, line, p) == Cmd.key.at(B.cb_st.of(None{}, q), t, line, p, sel, k) : Cmd.Out}, s)
    case Some{e}:
      {==}

# the walk over a declared path q (or the root) answers through the row
# of the selection at q
def kr_walked(q: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, ok: {Laws.cmd_wf(t) == True{} : Bool}, +on: {Laws.cmd_walks(t, q) == True{} : Bool}) -> {Cmd.key.row(Cmd.row(sel, t, q), k, t, line, p) == Cmd.key.at(Cmd.walk(q, t, Cmd.Top{}), t, line, p, sel, k) : Cmd.Out}:
  match q:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(Cmd.St, Cmd.walk(x <> rest, t, Cmd.Top{}), B.cb_st(t, x <> rest), B.cb_walk_root(x <> rest, t, ok, on)) : {Cmd.key.row(Cmd.row(sel, t, x <> rest), k, t, line, p) == Cmd.key.at(_, t, line, p, sel, k) : Cmd.Out}
      kr_st_of(Laws.cmd_lookup(t, x <> rest), x <> rest, t, line, p, sel, k, B.cb_walks_decl(rest, x, t, Nil{}, on))

# the line q p: Tab or Enter answers through the row of the selection at q
def kr_key(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, +ok: {Laws.cmd_wf(t) == True{} : Bool}, +on: {Laws.cmd_walks(t, q) == True{} : Bool}, word: {Laws.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.key.row(Cmd.row(sel, t, q), k, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == Cmd.key(t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), sel, k) : Cmd.Out}:
  %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(Cmd.words(Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])))), (q, p), B.cb_cut_last(t, q, p, ok, on, word)) : {Cmd.key.row(Cmd.row(sel, t, q), k, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == Cmd.key.cut(_, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), sel, k) : Cmd.Out}
  kr_walked(q, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p, sel, k, ok, on)

# a place whose entry is no child of q gives no row
def kr_miss_kid(e: Cmd.Ent, +q: List<&2, List<&2, Nat>>, s: {Laws.cmd_is_kid(q, Laws.cmd_ent_path(e)) == False{} : Bool}) -> {None{} == Cmd.row.kid(Cmd.kid(q, Cmd.Ent.path(e)), e) : Maybe<&2, Cmd.Ent>}:
  match e:
    case Cmd.Ent{+pp, a, r, f, g}:
      %Equal.sym(Bool, Cmd.kid(q, pp), Laws.cmd_is_kid(q, pp), B.cb_kid(q, pp)) : {None{} == Cmd.row.kid(_, Cmd.Ent{pp, a, r, f, g}) : Maybe<&2, Cmd.Ent>}
      %Equal.sym(Bool, Laws.cmd_is_kid(q, pp), False{}, s) : {None{} == Cmd.row.kid(_, Cmd.Ent{pp, a, r, f, g}) : Maybe<&2, Cmd.Ent>}
      {==}

def kr_miss_of(m: Maybe<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, s: {Laws.cmd_row.of(m, q) == False{} : Bool}) -> {None{} == Cmd.row.of(m, q) : Maybe<&2, Cmd.Ent>}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      kr_miss_kid(e, q, s)

# a place that holds the child e of q gives the row e
def kr_hit_kid(e: Cmd.Ent, +q: List<&2, List<&2, Nat>>, c: {Laws.cmd_is_kid(q, Laws.cmd_ent_path(e)) == True{} : Bool}) -> {Some{e} == Cmd.row.kid(Cmd.kid(q, Cmd.Ent.path(e)), e) : Maybe<&2, Cmd.Ent>}:
  match e:
    case Cmd.Ent{+pp, a, r, f, g}:
      %Equal.sym(Bool, Cmd.kid(q, pp), Laws.cmd_is_kid(q, pp), B.cb_kid(q, pp)) : {Some{Cmd.Ent{pp, a, r, f, g}} == Cmd.row.kid(_, Cmd.Ent{pp, a, r, f, g}) : Maybe<&2, Cmd.Ent>}
      %Equal.sym(Bool, Laws.cmd_is_kid(q, pp), True{}, c) : {Some{Cmd.Ent{pp, a, r, f, g}} == Cmd.row.kid(_, Cmd.Ent{pp, a, r, f, g}) : Maybe<&2, Cmd.Ent>}
      {==}

def kr_hit(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +i: Nat, +e: Cmd.Ent, at: {List.get(&2, Cmd.Ent, t, i) == Some{e} : Maybe<&2, Cmd.Ent>}, c: {Laws.cmd_is_kid(q, Laws.cmd_ent_path(e)) == True{} : Bool}) -> {Some{e} == Cmd.row(Cmd.Row{i}, t, q) : Maybe<&2, Cmd.Ent>}:
  %Equal.sym(Maybe<&2, Cmd.Ent>, List.get(&2, Cmd.Ent, t, i), Some{e}, at) : {Some{e} == Cmd.row.of(_, q) : Maybe<&2, Cmd.Ent>}
  kr_hit_kid(e, q, c)

def Laws.command_stale_row_ignored(t, q, p, i, k, ok, on, word, stale):
  +o = ok
  +n = on
  +w = word
  %kr_key(t, q, p, Cmd.Row{i}, k, o, n, w) : {_ == Cmd.key(t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), Cmd.NoRow{}, k) : Cmd.Out}
  %kr_key(t, q, p, Cmd.NoRow{}, k, o, n, w) : {Cmd.key.row(Cmd.row(Cmd.Row{i}, t, q), k, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == _ : Cmd.Out}
  %kr_miss_of(List.get(&2, Cmd.Ent, t, i), q, stale) : {Cmd.key.row(_, k, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == Cmd.key.row(None{}, k, t, Laws.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) : Cmd.Out}
  {==}
