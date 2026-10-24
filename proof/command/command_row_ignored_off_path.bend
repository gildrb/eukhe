# eukhe: the proof of LAW command_row_ignored_off_path
#
# PROOF of LAW command_row_ignored_off_path: the words of the line are
# the loose words of q with empty words among them, w, more and p (every
# word is spaceless; rio_words), so the cut keeps all but p. The walk
# skips the empty words at the root and at a declared path and lands on
# q (LSp.sp_walk_lsi); w, naming no child of q, lands on Stray at the
# root, else on Rest (q takes text) or Lost (LA.cb_step_miss), and each
# stays one of those whatever follows (LA.cb_walk_stray,
# LA.cb_walk_rest, LA.cb_walk_lost). There key.at answers key.bare,
# which never reads the selection: the row and no row act the same.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../base/bool.bend as LBool
import ../base/list.bend as LList
import ./base.bend as LA
import ./base/space.bend as LSp

def rio_free(b: Bool, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +more: List<&2, List<&2, Nat>>, -line: List<&2, Nat>, -p: List<&2, Nat>, -sel: Cmd.Sel, -k: Cmd.Press) -> {Cmd.key.at(Cmd.walk(more, t, Cmd.step.miss(b, q, w)), t, line, p, sel, k) == Cmd.key.bare(k, t, line) : Cmd.Out}:
  match b:
    case True{}:
      %Equal.sym(Cmd.St, Cmd.walk(more, t, Cmd.Rest{q, [w]}), Cmd.Rest{q, w <> more}, LA.cb_walk_rest(more, t, q, [w])) : {Cmd.key.at(_, t, line, p, sel, k) == Cmd.key.bare(k, t, line) : Cmd.Out}
      {==}
    case False{}:
      %Equal.sym(Cmd.St, Cmd.walk(more, t, Cmd.Lost{q, w}), Cmd.Lost{q, w}, LA.cb_walk_lost(more, t, q, w)) : {Cmd.key.at(_, t, line, p, sel, k) == Cmd.key.bare(k, t, line) : Cmd.Out}
      {==}

# after a word that names no child of q, Tab and Enter act as with no row
def rio_miss(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +more: List<&2, List<&2, Nat>>, -line: List<&2, Nat>, -p: List<&2, Nat>, -sel: Cmd.Sel, -k: Cmd.Press) -> {Cmd.key.at(Cmd.walk(more, t, LA.cb_miss(t, q, w)), t, line, p, sel, k) == Cmd.key.bare(k, t, line) : Cmd.Out}:
  match q:
    case Nil{}:
      %Equal.sym(Cmd.St, Cmd.walk(more, t, Cmd.Stray{}), Cmd.Stray{}, LA.cb_walk_stray(more, t)) : {Cmd.key.at(_, t, line, p, sel, k) == Cmd.key.bare(k, t, line) : Cmd.Out}
      {==}
    case Con{+y, +ys}:
      rio_free(Command.cmd_free(t, y <> ys), t, y <> ys, w, more, line, p, sel, k)

# the words of the line: the loose words of q, w and more before p
def rio_words(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +more: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +gs: List<&2, Nat>, ok: {Command.cmd_wf(t) == True{} : Bool}, on: {Command.cmd_walks(t, q) == True{} : Bool}, word: {Command.cmd_typed(w) == True{} : Bool}, after: {Command.cmd_all_spaceless(more) == True{} : Bool}, last: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.words(List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), Command.cmd_sep(List.append(&2, List<&2, Nat>, more, [p])))) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, LSp.sp_lsi(q, gs), w <> more), [p]) : List<&2, List<&2, Nat>>}:
  -m = List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), Command.cmd_sep(List.append(&2, List<&2, Nat>, more, [p])))
  +mp = List.append(&2, List<&2, Nat>, more, [p])
  +li = LSp.sp_lsi(q, gs)
  %Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, li, w <> more), [p]), List.append(&2, List<&2, Nat>, li, List.append(&2, List<&2, Nat>, w <> more, [p])), LList.cb_app_assoc(List<&2, Nat>, li, w <> more, [p])) : {Cmd.words(m) == _ : List<&2, List<&2, Nat>>}
  %LList.cb_app_assoc(List<&2, Nat>, li, [w], mp) : {Cmd.words(m) == _ : List<&2, List<&2, Nat>>}
  %LSp.sp_ls_last(q, w, gs) : {Cmd.words(m) == List.append(&2, List<&2, Nat>, _, mp) : List<&2, List<&2, Nat>>}
  +hqw = LA.cb_all_spaceless_app(q, [w], LA.cb_names_spaceless(q, LA.cb_walks_names(t, q, ok, on)), LBool.cb_and_intro(Command.cmd_spaceless(w), True{}, LA.cb_typed_spaceless(w, word), {==}))
  +hmp = LA.cb_all_spaceless_app(more, [p], after, LBool.cb_and_intro(Command.cmd_spaceless(p), True{}, last, {==}))
  LSp.sp_words_loose_last(q, w, gs, Command.cmd_sep(mp), mp, hqw, LA.cb_words_sep(mp, hmp))

# the walk over the words before p: the miss state of w, then more
def rio_walk(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +more: List<&2, List<&2, Nat>>, +gs: List<&2, Nat>, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}, word: {Command.cmd_typed(w) == True{} : Bool}, miss: {Command.cmd_takes(t, q, Command.cmd_lower(w)) == False{} : Bool}) -> {Cmd.walk(List.append(&2, List<&2, Nat>, LSp.sp_lsi(q, gs), w <> more), t, Cmd.Top{}) == Cmd.walk(more, t, LA.cb_miss(t, q, w)) : Cmd.St}:
  +li = LSp.sp_lsi(q, gs)
  %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, li, w <> more), t, Cmd.Top{}), Cmd.walk(w <> more, t, Cmd.walk(li, t, Cmd.Top{})), LA.cb_walk_app(li, w <> more, t, Cmd.Top{})) : {_ == Cmd.walk(more, t, LA.cb_miss(t, q, w)) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.walk(li, t, Cmd.Top{}), LA.cb_st(t, q), LSp.sp_walk_lsi(q, gs, t, Nil{}, ok, {==}, on)) : {Cmd.walk(w <> more, t, _) == Cmd.walk(more, t, LA.cb_miss(t, q, w)) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.step(LA.cb_st(t, q), t, w), LA.cb_miss(t, q, w), LA.cb_step_miss(t, q, w, LA.cb_walks_at(t, q, on), word, miss)) : {Cmd.walk(more, t, _) == Cmd.walk(more, t, LA.cb_miss(t, q, w)) : Cmd.St}
  {==}

# Tab or Enter on the line, with any selection, acts as with no row
def rio_bare(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +more: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +gs: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}, +word: {Command.cmd_typed(w) == True{} : Bool}, after: {Command.cmd_all_spaceless(more) == True{} : Bool}, last: {Command.cmd_spaceless(p) == True{} : Bool}, miss: {Command.cmd_takes(t, q, Command.cmd_lower(w)) == False{} : Bool}) -> {Cmd.key(t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), Command.cmd_sep(List.append(&2, List<&2, Nat>, more, [p]))), sel, k) == Cmd.key.bare(k, t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), Command.cmd_sep(List.append(&2, List<&2, Nat>, more, [p])))) : Cmd.Out}:
  +m = List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), Command.cmd_sep(List.append(&2, List<&2, Nat>, more, [p])))
  +d = List.append(&2, List<&2, Nat>, LSp.sp_lsi(q, gs), w <> more)
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(m), List.append(&2, List<&2, Nat>, d, [p]), rio_words(t, q, w, more, p, gs, ok, on, word, after, last)) : {Cmd.key.cut(Cmd.cut(_), t, m, sel, k) == Cmd.key.bare(k, t, m) : Cmd.Out}
  %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(List.append(&2, List<&2, Nat>, d, [p])), (d, p), LA.cb_cut(d, p)) : {Cmd.key.cut(_, t, m, sel, k) == Cmd.key.bare(k, t, m) : Cmd.Out}
  %Equal.sym(Cmd.St, Cmd.walk(d, t, Cmd.Top{}), Cmd.walk(more, t, LA.cb_miss(t, q, w)), rio_walk(t, q, w, more, gs, ok, on, word, miss)) : {Cmd.key.at(_, t, m, p, sel, k) == Cmd.key.bare(k, t, m) : Cmd.Out}
  rio_miss(t, q, w, more, m, p, sel, k)

def Command.command_row_ignored_off_path(t, q, w, more, p, gs, i, k, ok, on, word, after, last, miss):
  +m = List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), Command.cmd_sep(List.append(&2, List<&2, Nat>, more, [p])))
  +o = ok
  +n = on
  +wd = word
  +af = after
  +la = last
  +ms = miss
  Equal.trans(Cmd.Out, Cmd.key(t, m, Cmd.Row{i}, k), Cmd.key.bare(k, t, m), Cmd.key(t, m, Cmd.NoRow{}, k), rio_bare(t, q, w, more, p, gs, Cmd.Row{i}, k, o, n, wd, af, la, ms), Equal.sym(Cmd.Out, Cmd.key(t, m, Cmd.NoRow{}, k), Cmd.key.bare(k, t, m), rio_bare(t, q, w, more, p, gs, Cmd.NoRow{}, k, o, n, wd, af, la, ms)))
